import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.H0IsIffNonemptyLinearEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleTrivialization
section
namespace GlobalTheory.CubeCoc

theorem symm_cocycle_add (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [AddCommGroup A]
    (f : X → X → A) (hs : ∀ a b, f a b = f b a)
    (hc : ∀ a b c, f (a + b) c + f a b = f a (b + c) + f b c) :
    ∃ g : X → A, ∀ a b, f a b = g (a + b) - g a - g b := by
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cocycle_isCoboundary X (Multiplicative A)
    (fun a b => Multiplicative.ofAdd (f a b)) (fun a b => by rw [hs]) (fun a b c => by
      show Multiplicative.ofAdd (f (a + b) c + f a b) = Multiplicative.ofAdd (f a (b + c) + f b c)
      rw [hc])
  refine ⟨fun x => Multiplicative.toAdd (g x), fun a b => ?_⟩
  have h := congrArg Multiplicative.toAdd (hg a b)
  simpa [sub_eq_add_neg] using h

theorem ext_of_basis {X : Type} [AddCommGroup X] {ι : Type} (bs : Module.Basis ι ℤ X)
    {M : Type} [AddCommGroup M] (φ ψ : X → M) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (hψ : ∀ a b, ψ (a + b) = ψ a + ψ b) (h : ∀ i, φ (bs i) = ψ (bs i)) : ∀ a, φ a = ψ a := by
  have e := bs.ext (f₁ := (AddMonoidHom.mk' φ hφ).toIntLinearMap)
    (f₂ := (AddMonoidHom.mk' ψ hψ).toIntLinearMap) h
  intro a
  exact LinearMap.congr_fun e a

variable {X : Type} [AddCommGroup X] {A : Type} [AddCommGroup A]

theorem cubical_add [Module.Free ℤ X] (f : X → X → X → A)
    (hs1 : ∀ a b c, f a b c = f b a c) (hs2 : ∀ a b c, f a b c = f a c b)
    (hc : ∀ x x' x'' y, f (x + x') x'' y + f x x' y = f x (x' + x'') y + f x' x'' y) :
    ∃ g : X → A, ∀ a a' b, f a a' b + (g (a + a') + g (a + b) + g (a' + b))
      = g (a + a' + b) + g a + g a' + g b := by
  have hcyc : ∀ a b c, f a b c = f b c a := fun a b c => by rw [hs1, hs2]

  obtain ⟨T, hT⟩ := symm_cocycle_add X (X → A) (fun a a' b => f a a' b)
    (fun a b => funext fun c => hs1 a b c)
    (fun a b c => funext fun y => by simpa using hc a b c y)
  have ht1 : ∀ a a' b, f a a' b = T (a + a') b - T a b - T a' b := fun a a' b => by
    simpa using congrFun (hT a a') b

  have hcomp : ∀ a a' b b', f a a' (b + b') + f a b b' + f a' b b'
      = f (a + a') b b' + f a a' b + f a a' b' := fun a a' b b' => by
    have c1 := hc a a' b b'
    have c2 := hc a' b b' a
    have e1 : f a (a' + b) b' = f (a' + b) b' a := hcyc _ _ _
    have e2 : f a' b a = f a a' b := (hcyc _ _ _).symm
    have e3 : f a' (b + b') a = f a a' (b + b') := (hcyc _ _ _).symm
    have e4 : f b b' a = f a b b' := (hcyc _ _ _).symm
    linear_combination (norm := module) -c1 - c2 - e1 + e2 - e3 - e4

  let d : X → X → X → A := fun a b b' => T a (b + b') - T a b - T a b' - f a b b'
  have hd_add : ∀ a a' b b', d (a + a') b b' = d a b b' + d a' b b' := fun a a' b b' => by
    have u1 := ht1 a a' (b + b')
    have u2 := ht1 a a' b
    have u3 := ht1 a a' b'
    have u4 := hcomp a a' b b'
    simp only [d]
    linear_combination (norm := module) -u1 + u2 + u3 + u4
  have hd_cob : ∀ a, ∃ h : X → A, ∀ b b', d a b b' = h (b + b') - h b - h b' := fun a => by
    refine symm_cocycle_add X A (d a) (fun b b' => by simp only [d]; rw [add_comm b b', hs2]; abel)
      (fun b b' b'' => ?_)
    have c := hc b b' b'' a
    have e1 : f (b + b') b'' a = f a (b + b') b'' := (hcyc _ _ _).symm
    have e2 : f b b' a = f a b b' := (hcyc _ _ _).symm
    have e3 : f b (b' + b'') a = f a b (b' + b'') := (hcyc _ _ _).symm
    have e4 : f b' b'' a = f a b' b'' := (hcyc _ _ _).symm
    simp only [d]
    rw [add_assoc b b' b'']
    linear_combination (norm := module) -c + e1 + e2 - e3 - e4
  let bs := Module.Free.chooseBasis ℤ X
  choose h hh using fun i => hd_cob (bs i)
  let H : X →ₗ[ℤ] (X → A) := bs.constr ℤ h
  have hHb : ∀ i, H (bs i) = h i := fun i => bs.constr_basis ℤ h i
  have hH : ∀ a b b', d a b b' = H a (b + b') - H a b - H a b' := fun a b b' => by
    refine ext_of_basis bs (fun a => d a b b') (fun a => H a (b + b') - H a b - H a b')
      (fun a a' => hd_add a a' b b') (fun a a' => ?_) (fun i => ?_) a
    · simp only [map_add, Pi.add_apply]; abel
    · simp only [hHb]; exact hh i b b'
  let t' : X → X → A := fun a b => T a b - H a b
  have hL1 : ∀ a a' b, f a a' b = t' (a + a') b - t' a b - t' a' b := fun a a' b => by
    simp only [t', map_add, Pi.add_apply]; rw [ht1]; abel
  have hL2 : ∀ a b b', f a b b' = t' a (b + b') - t' a b - t' a b' := fun a b b' => by
    have := hH a b b'
    simp only [d] at this
    simp only [t']
    linear_combination (norm := module) -this

  let s : X → X → A := fun a b => t' a b - t' b a
  have hs_l : ∀ a a' b, s (a + a') b = s a b + s a' b := fun a a' b => by
    have e : f b a a' = f a a' b := hcyc b a a'
    have u1 := hL1 a a' b
    have u2 := hL2 b a a'
    simp only [s]
    linear_combination (norm := module) -u1 + u2 - e
  have hs_r : ∀ a b b', s a (b + b') = s a b + s a b' := fun a b b' => by
    have e : f b b' a = f a b b' := (hcyc a b b').symm
    have u1 := hL2 a b b'
    have u2 := hL1 b b' a
    simp only [s]
    linear_combination (norm := module) -u1 + u2 - e
  classical
  let v : Module.Free.ChooseBasisIndex ℤ X → Module.Free.ChooseBasisIndex ℤ X → A :=
    fun i j => if WellOrderingRel i j then s (bs i) (bs j) else 0
  let U : X →ₗ[ℤ] X →ₗ[ℤ] A := bs.constr ℤ (fun i => bs.constr ℤ (v i))
  have hU : ∀ i j, U (bs i) (bs j) = v i j := by
    intro i j; simp only [U, Module.Basis.constr_basis]
  have hi : ∀ i b, s (bs i) b = U (bs i) b - U b (bs i) := by
    intro i b
    refine ext_of_basis bs (fun b => s (bs i) b) (fun b => U (bs i) b - U b (bs i))
      (fun b b' => hs_r _ b b') (fun b b' => by simp only [map_add, LinearMap.add_apply]; abel)
      (fun j => ?_) b
    show s (bs i) (bs j) = U (bs i) (bs j) - U (bs j) (bs i)
    rw [hU, hU]
    rcases trichotomous_of WellOrderingRel i j with h | h | h
    · have h' : ¬ WellOrderingRel j i := asymm h
      simp only [v, if_pos h, if_neg h', sub_zero]
    · subst h; simp only [s, sub_self]
    · have h' : ¬ WellOrderingRel i j := asymm h
      simp only [v, if_pos h, if_neg h', s]; abel
  have hsu : ∀ a b, s a b = U a b - U b a := fun a b =>
    ext_of_basis bs (fun a => s a b) (fun a => U a b - U b a) (fun a a' => hs_l a a' b)
      (fun a a' => by simp only [map_add, LinearMap.add_apply]; abel) (fun i => hi i b) a
  let t'' : X → X → A := fun a b => t' a b - U a b
  have hsym : ∀ a b, t'' a b = t'' b a := fun a b => by
    have := hsu a b
    simp only [s] at this
    simp only [t'']
    linear_combination (norm := module) this
  have hM1 : ∀ a a' b, f a a' b = t'' (a + a') b - t'' a b - t'' a' b := fun a a' b => by
    simp only [t'', map_add, LinearMap.add_apply]; rw [hL1]; abel
  have hM2 : ∀ a b b', f a b b' = t'' a (b + b') - t'' a b - t'' a b' := fun a b b' => by
    simp only [t'', map_add]; rw [hL2]; abel
  have hcoc : ∀ a b c, t'' (a + b) c + t'' a b = t'' a (b + c) + t'' b c := fun a b c => by
    have u1 := hM1 a b c
    have u2 := hM2 a b c
    linear_combination (norm := module) u2 - u1
  obtain ⟨g, hg⟩ := symm_cocycle_add X A t'' hsym hcoc
  refine ⟨g, fun a a' b => ?_⟩
  rw [hM1 a a' b, hg (a + a') b, hg a b, hg a' b]
  abel

end GlobalTheory.CubeCoc

namespace GlobalTheory

theorem symm_cubical_cocycle_isThirdDifference : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → X → A), (∀ a b c, f a b c = f b a c) → (∀ a b c, f a b c = f a c b) → (∀ x x' x'' y, f (x + x') x'' y * f x x' y = f x (x' + x'') y * f x' x'' y) → ∃ g : X → A, ∀ a a' b, f a a' b * (g (a + a') * g (a + b) * g (a' + b)) = g (a + a' + b) * g a * g a' * g b := by
  intro X _ _ A _ f hs1 hs2 hc
  obtain ⟨g, hg⟩ := CubeCoc.cubical_add (A := Additive A) (fun a b c => Additive.ofMul (f a b c))
    (fun a b c => by rw [hs1]) (fun a b c => by rw [hs2])
    (fun x x' x'' y => by
      show Additive.ofMul (f (x + x') x'' y * f x x' y) = Additive.ofMul (f x (x' + x'') y * f x' x'' y)
      rw [hc])
  exact ⟨fun x => Additive.toMul (g x), fun a a' b => congrArg Additive.toMul (hg a a' b)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  first | exact @GlobalTheory.SymGrpPull.symm_pull | exact GlobalTheory.SymGrpPull.symm_pull | (intros; apply GlobalTheory.SymGrpPull.symm_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPullbackGeneratorEvenValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem uw_even_val : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw x⁻¹.left z J * val D₀.sym x.left z J * cubV D₀.cub z J (x ≫ f) (x ≫ f)⁻¹ x⁻¹ =
        val uw x.left z J * cubV D₀.cub z J x x⁻¹ (x ≫ f) := by
  intro R _ _ D₀ f _ uw hu h₀ T x z J hJ
  let gL := LB.mulGen D₀.P.L _ _ _ _
      (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw ((𝟙 D₀.P.A)⁻¹).left) D₀.sym)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift f (lift f⁻¹ (𝟙 D₀.P.A)⁻¹)).left)
  let gR := LB.mulGen D₀.P.L _ _ _ _ uw
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (𝟙 D₀.P.A) (lift (𝟙 D₀.P.A)⁻¹ f)).left)
  have ev : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gL σ.left z J = val uw (σ ≫ (𝟙 D₀.P.A)⁻¹).left z J * val D₀.sym σ.left z J *
          cubV D₀.cub z J (σ ≫ f) (σ ≫ f⁻¹) (σ ≫ (𝟙 D₀.P.A)⁻¹) ∧
        val gR σ.left z J = val uw σ.left z J *
          cubV D₀.cub z J (σ ≫ 𝟙 D₀.P.A) (σ ≫ (𝟙 D₀.P.A)⁻¹) (σ ≫ f) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_pull hJ _ _ _) rfl)) (val_cub D₀.cub σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub σ hJ _ _ _))⟩

  have pw : ∀ (V : Type) [CommGroup V] (k : (D₀.P.A.left ⟶ D₀.P.A.left) → V) (σ : D₀.P.A ⟶ D₀.P.A),
      ∏ i, k (σ.left ≫ w0φ D₀ f i) ^ w0ε i =
        k (σ * (σ ≫ f)).left * (k σ.left)⁻¹ * (k σ.left)⁻¹ * (k (σ ≫ f).left)⁻¹ *
          k (1 : D₀.P.A ⟶ D₀.P.A).left * k (1 : D₀.P.A ⟶ D₀.P.A).left := by
    intro V _ k σ
    have e₀ : σ.left ≫ (padd D₀.P.A (𝟙 _) f).left = (σ * (σ ≫ f)).left :=
      congrArg (fun q : D₀.P.A ⟶ D₀.P.A => q.left) ((MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
    have e₃ : σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : D₀.P.A ⟶ D₀.P.A).left := by
      rw [← Over.comp_left]; congr 1; simp [Hom.one_def]
    rw [Fin.prod_univ_four]
    show k (σ.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * k (σ.left ≫ 𝟙 _) ^ (-2 : ℤ) *
      k (σ.left ≫ f.left) ^ (-1 : ℤ) * k (σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
    rw [e₀, e₃, Category.comp_id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.comp_left]
    abel
  have hL : val gL x.left z J = val gR x.left z J := by
    refine gen_unique' D₀.P.isLB (u := gL) (u' := gR) ?_ D₀.P.A.hom (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left
      (Over.w (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)) (GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2 ?_ ?_ ?_ T.left x.left z J hJ
    · intro V _ k
      have pw0 : ∏ i, k (w0φ D₀ f i) ^ w0ε i = _ :=
        (Finset.prod_congr rfl fun i _ => by rw [Over.id_left, Category.id_comp]).trans (pw V k (𝟙 D₀.P.A))
      have ps : ∏ i : Fin 2, k (![(ι[D₀.P.A]).left, 𝟙 D₀.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
          k (Over.Hom.left (𝟙 D₀.P.A)⁻¹) * (k (Over.Hom.left (𝟙 D₀.P.A)))⁻¹ := by
        have : (𝟙 D₀.P.A)⁻¹ = ι[D₀.P.A] := by simp [Hom.inv_def]
        rw [Fin.prod_univ_two, this]
        simp
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ pw0 (prod_cub _ _ _ k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 2) (K' := thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ (pw V k _) ps) (prod_cub _ _ _ k)).symm)
      have a1 : 𝟙 D₀.P.A ≫ f = f := Category.id_comp f
      have a2 : (𝟙 D₀.P.A)⁻¹ ≫ f = f⁻¹ := by rw [GrpObj.inv_comp, Category.id_comp]
      have a3 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ * f = f := by group
      have a4 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ = 1 := by group
      have a5 : f * f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ := by group
      have a6 : f * f⁻¹ = 1 := by group
      have a7 : f * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f := mul_comm _ _
      have a8 : f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f⁻¹ := mul_comm _ _
      rw [a1, a2, a3, a4, a5, a6, a7, a8]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) D₀.sym_gen)
        (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · intro y I hI
      have C : IsCub (cubV D₀.cub (T := 𝟙_ _) y I) := isCub_cubV D₀.cub hI
      have o : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left = eSec D₀.P.A := by simp [Hom.one_def, eSec]
      have u1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI h₀ (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have s1 : val D₀.sym (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI D₀.sym_rig (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have i1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ (𝟙 D₀.P.A)⁻¹ = 1 := by
        rw [GrpObj.comp_inv, Category.comp_id, inv_one]
      have f1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ f⁻¹ = 1 := by
        rw [GrpObj.comp_inv, MonObj.one_comp, inv_one]
      rw [(ev _ hI).1, (ev _ hI).2, i1, f1, MonObj.one_comp, Category.comp_id, u1, s1, C.face]; simp only [_root_.mul_one]
  have := (ev x hJ).1.symm.trans (hL.trans (ev x hJ).2)
  rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id] at this

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPullbackGeneratorSecondDifference
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UTau0.SecondDiff

theorem prod_symmetricPullback_formalSum_eq {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) {T : Over (Sp R)}
    (q : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D₀.P.A.left) → U) :
    ∏ i, h (q.left ≫ GlobalTheory.UTau0.w0φ D₀ f i) ^ GlobalTheory.UTau0.w0ε i =
      h (q * (q ≫ f)).left * (h q.left ^ 2)⁻¹ * (h (q ≫ f).left)⁻¹ * h (1 : T ⟶ D₀.P.A).left ^ 2 := by
  have e₀ : q.left ≫ (padd D₀.P.A (𝟙 _) f).left = (q * (q ≫ f)).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ padd D₀.P.A (𝟙 _) f = q * (q ≫ f) from (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
  have e₃ : q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : T ⟶ D₀.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ toUnit D₀.P.A ≫ η[D₀.P.A] = 1 by rw [Hom.one_def, ← Category.assoc, comp_toUnit])
  rw [Fin.prod_univ_four]
  show h (q.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * h (q.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (q.left ≫ f.left) ^ (-1 : ℤ) * h (q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
  rw [e₀, e₃, Category.comp_id, ← Over.comp_left]
  simp only [zpow_one, zpow_neg, zpow_ofNat, pow_one]

theorem uw_second_diff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f g : D₀.P.A ⟶ D₀.P.A) [IsMonHom f] [IsMonHom g],
    padd D₀.P.A f g = 𝟙 D₀.P.A →
    ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A f g) rosatiε), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x x' : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw (x * x').left z J * cubV D₀.cub z J (x' ≫ f) (x' ≫ g) x =
        val uw x.left z J * val uw x'.left z J * val u (lift x x').left z J *
          cubV D₀.cub z J (x ≫ f) (x' ≫ f) x * cubV D₀.cub z J (x ≫ f) (x' ≫ f) x' *
          cubV D₀.cub z J x x' ((x ≫ f) * (x' ≫ f)) := by
  intro R _ _ D₀ f g _ _ hfg uw huw hw0 u hu hu0 T x x' z J hJ
  let p₀ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := fst _ _
  let p₁ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := snd _ _
  have mf : ∀ {T : Over (Sp R)} (a b : T ⟶ D₀.P.A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => MonObj.mul_comp a b f
  have fg : ∀ {T : Over (Sp R)} (a : T ⟶ D₀.P.A), (a ≫ f) * (a ≫ g) = a := fun a =>
    (MonObj.comp_mul _ _ _).symm.trans ((congrArg (a ≫ ·) (show f * g = 𝟙 _ from hfg)).trans (Category.comp_id a))
  let gLw := LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (p₀ * p₁).left)
    (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₁ ≫ f) (lift (p₁ ≫ g) p₀)).left)
  let gRw := LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw p₀.left)
      (LB.pullGen D₀.P.L _ _ uw p₁.left)) (LB.pullGen D₀.P.L _ _ u (lift p₀ p₁).left))
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₀)).left)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₁)).left))
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift p₀ (lift p₁ ((p₀ ≫ f) * (p₁ ≫ f)))).left))
  have vq : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      ∀ {K : Type} [Fintype K] {φ : K → (D₀.P.A.left ⟶ D₀.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D₀.P.L φ ε))
        (q : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A), val (LB.pullGen D₀.P.L _ _ t q.left) σ.left z J = val t (σ ≫ q).left z J :=
    fun σ z J hJ K _ φ ε t q => by rw [val_pull hJ, ← Over.comp_left]
  have evL : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gLw σ.left z J = val uw (σ ≫ (p₀ * p₁)).left z J *
        cubV D₀.cub z J (σ ≫ p₁ ≫ f) (σ ≫ p₁ ≫ g) (σ ≫ p₀) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (val_cub D₀.cub σ hJ _ _ _))
  have evR : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gRw σ.left z J = val uw (σ ≫ p₀).left z J * val uw (σ ≫ p₁).left z J *
          val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J *
        (cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₀) * cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₁) *
          cubV D₀.cub z J (σ ≫ p₀) (σ ≫ p₁) (σ ≫ ((p₀ ≫ f) * (p₁ ≫ f)))) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (vq σ hJ _ _)))
      (by rw [val_pull hJ, ← Over.comp_left, comp_lift])))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub D₀.cub σ hJ _ _ _) (val_cub D₀.cub σ hJ _ _ _))) (val_cub D₀.cub σ hJ _ _ _))))

  let e : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A ⊗ D₀.P.A := lift 1 1
  have he : e.left ≫ (snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
  have sj : Function.Surjective ((snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom).appTop.hom :=
    surj_comp (surj_snd GlobalTheory.globalFns_holds D₀.P.isAb _) ((GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2)
  let ρ : T ⟶ D₀.P.A ⊗ D₀.P.A := lift x x'
  have key : val gLw ρ.left z J = val gRw ρ.left z J := by
    refine gen_unique' D₀.P.isLB (fun V _ k => ?_) _ e.left he sj ?_ ?_ (fun y I hI => ?_) _ ρ.left z J hJ
    · refine Eq.trans (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ Fin 6) (K' := (thK ⊕ thK) ⊕ thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 6) (U := V) _
            (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f p₀ k) (prod_symmetricPullback_formalSum_eq D₀ f p₁ k))
            (prod_ros f g p₀ p₁ k))
          (DVR.prod_sum₂ (K := thK ⊕ thK) (K' := thK) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₀ k)
              (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₁ k))
            (prod_cub p₀ p₁ ((p₀ ≫ f) * (p₁ ≫ f)) k)))
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f (p₀ * p₁) k)
          (prod_cub (p₁ ≫ f) (p₁ ≫ g) p₀ k)).symm)
      rw [mf, fg, mul_comm p₁ p₀, mul_comm (p₀ ≫ f) p₀, mul_comm (p₁ ≫ f) p₁, mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₀,
        mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₁, mul_comm (p₁ ≫ g) p₀]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ huw _)) (DVR.pullGen_isGen _ _ _ _ hu _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
          (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _))
    · have C : IsCub (cubV D₀.cub y I) := isCub_cubV D₀.cub hI
      have w1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI hw0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by simp [Hom.one_def]
        rw [e1]; exact this
      have u1 : val u (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1).left y I = 1 := by
        have := val_corr hI hu0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e2 : lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1 = lift η[D₀.P.A] η[D₀.P.A] := by simp [Hom.one_def]
        rw [e2]; exact this
      have a₀ : e ≫ p₀ = 1 := lift_fst _ _
      have a₁ : e ≫ p₁ = 1 := lift_snd _ _
      have af : e ≫ p₀ ≫ f = 1 := by rw [← Category.assoc, a₀, MonObj.one_comp]
      have bf : e ≫ p₁ ≫ f = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have bg : e ≫ p₁ ≫ g = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have ab : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
      have ff : e ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [af, bf, _root_.mul_one])
      rw [evL e hI, evR e hI, ab, ff, af, bf, bg, a₀, a₁, w1, u1, C.face]
      simp
  rw [evL ρ hJ, evR ρ hJ] at key
  have r₀ : ρ ≫ p₀ = x := lift_fst _ _
  have r₁ : ρ ≫ p₁ = x' := lift_snd _ _
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  have s₂ : ρ ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = (x ≫ f) * (x' ≫ f) :=
    (MonObj.comp_mul _ _ _).trans (by rw [← Category.assoc, ← Category.assoc, r₀, r₁])
  rw [s₁, s₂, ← Category.assoc ρ p₁ f, ← Category.assoc ρ p₁ g, ← Category.assoc ρ p₀ f, r₀, r₁] at key
  rw [key]
  simp only [_root_.mul_assoc]

end GlobalTheory.UTau0.SecondDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_twoCocycle_free_abelian_isCoboundary : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → A), (∀ a b, f a b = f b a) → (∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) → ∃ g : X → A, ∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ := by
  first | exact @GlobalTheory.symm_cocycle_isCoboundary | exact GlobalTheory.symm_cocycle_isCoboundary | (intros; apply GlobalTheory.symm_cocycle_isCoboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleSumPowMulStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul : ∀ (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D), (∀ x y, c x y = c y x) → (∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) → ∀ (n : ℕ) (x y : Γ), ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y = ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y + c (x ^ n) (y ^ n) - c 1 1 := by
  first | exact @GlobalTheory.TwoCocycle.sum_pow_mul | exact GlobalTheory.TwoCocycle.sum_pow_mul | (intros; apply GlobalTheory.TwoCocycle.sum_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryCubicalBundleOfDenseAbelianNormalBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base : ∀ {S U : Scheme.{0}} [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (F : A.left ⟶ G.left), IsGrpPullback A G j F → GlobalFnsSt → IsAbelianScheme A → ∀ (L : RigLB G) (c : CubicalStr G L) (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), sym.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J = cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J := by
  first | exact @GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | exact GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | (intros; apply GlobalTheory.SymCubDense.sym_cub_of_dense_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySecondDifferenceEqCubicalRatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ = val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  first | exact @GlobalTheory.PolDeg.SymCube.sym_cube | exact GlobalTheory.PolDeg.SymCube.sym_cube | (intros; apply GlobalTheory.PolDeg.SymCube.sym_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChartStatement
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
theorem _root_.GlobalTheory.T.tangent_derivation_affine_chart : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  first | exact @GlobalTheory.KSPkg.ksPackage | exact GlobalTheory.KSPkg.ksPackage | (intros; apply GlobalTheory.KSPkg.ksPackage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauPeriodValNegCubicalRatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tau_period_val_neg_cubical_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  first | exact @GlobalTheory.TauNeg.val_tau_neg | exact GlobalTheory.TauNeg.val_tau_neg | (intros; apply GlobalTheory.TauNeg.val_tau_neg <;> assumption)
end

