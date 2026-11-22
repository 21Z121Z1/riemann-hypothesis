import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.LamTransl
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem foldr_eq {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (l : List (Fin n)) :
    l.foldr (fun k acc => padd G (x k) acc) (pzero G T) = (l.map x).prod := by
  induction l with
  | nil => simp [pzero, Hom.one_def]
  | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, padd, Hom.mul_def]

def split3 (I : Finset (Fin 3)) : Finset (Fin 2) ⊕ Finset (Fin 2) :=
  if (2 : Fin 3) ∈ I then Sum.inl (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)
  else Sum.inr (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)

theorem split3_bij : Function.Bijective split3 := by decide

def splitEquiv : thK ≃ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.ofBijective _ split3_bij).trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

theorem mem8 : ∀ I : Finset (Fin 3),
    I ∈ ({∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))) := by decide

variable (a : 𝟙_ (Over S) ⟶ G)

def tr : G ⟶ G := (toUnit G ≫ a) * 𝟙 G

def pt3 : G2 G ⟶ G3 G := lift (fst G G) (lift (snd G G) (toUnit (G2 G) ≫ a))
def φA : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down ≫ tr G a).left
def φB : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left
def ε2 : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem splitEquiv_apply (I : Finset (Fin 3)) : splitEquiv ⟨I⟩ = Sum.map ULift.up ULift.up (split3 I) := by
  rfl

theorem split_eq (k : thK) : Sum.elim (φA G a) (φB G) (splitEquiv k) = (pt3 G a).left ≫ thφ G (x3 G) k ∧
    Sum.elim ε2 (fun k => -ε2 k) (splitEquiv k) = thε k := by
  rcases k with ⟨I⟩
  rw [splitEquiv_apply]
  have h := mem8 I
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [split3, if_true, if_false, Finset.mem_insert, Finset.mem_singleton,
      Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  all_goals
    refine ⟨?_, trivial⟩
    simp only [φA, φB, thφ]
    rw [← Over.comp_left]
    congr 1
    rw [psum, foldr_eq, psum, foldr_eq]
    simp [List.finRange_succ, x2, x3, pt3, tr, MonObj.comp_mul]
  all_goals ac_rfl

theorem sameSum : LB.SameSum (fun k => (pt3 G a).left ≫ thφ G (x3 G) k) thε (Sum.elim (φA G a) (φB G))
    (Sum.elim ε2 fun k => -ε2 k) := by
  classical
  intro ψ
  rw [← Equiv.sum_comp splitEquiv]
  exact Finset.sum_congr rfl fun k _ => by rw [(split_eq G a k).1, (split_eq G a k).2]

end GlobalTheory.Mum.LamTransl

namespace GlobalTheory.Mum

open LamTransl in

theorem lam_transl_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L →
    ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) →
      LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  intro S G _ _ L c a N hN hNL
  have hT : (L.L.pull (tr G a).left).IsLB := pull_isLB L.isLB _
  have hA : (LB.LinComb L.L (φA G a) ε2).IsLB := DVR.linComb_isLB _ L.isLB _ _
  have hLam := GlobalTheory.SabBaseChange.cube_isLB (x2 G) L.isLB
  have h1 : LBIso (abelian₂ G N) (abelian₂ G (L.L.pull (tr G a).left)) := GlobalTheory.SabBaseChange.lbIso_cube (x2 G) hNL
  have h2 : LBIso (abelian₂ G (L.L.pull (tr G a).left)) (LB.LinComb L.L (φA G a) ε2) :=
    LBIso.chartPull (chartPullLinComb L.L (tr G a).left _ (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (chartPullSame L.L (φA G a) (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (GlobalTheory.PolBaseChange.lbIso_refl hA)
  have h3 : LBIso (abelian₂ G L.L) (LB.LinComb L.L (φA G a) ε2) := by
    refine (GlobalTheory.TripleCompare.lbIso_iff_gen (L := L.L) (φB G) ε2 (φA G a) ε2).2 ?_
    obtain ⟨t', ht', -⟩ := DVR.gen_transport L.isLB (sameSum G a)
      _ (DVR.pullGen_isGen L.L _ _ c.t c.isGen (pt3 G a).left)
    exact ⟨t', ht'⟩
  exact LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hN) (GlobalTheory.SabBaseChange.cube_isLB _ hT) hLam h1
    (LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hT) hA hLam h2 (LBIso.symm h3))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CubeSymDescent

theorem of_push : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  intro S S' G G' _ _ _ _ f β h L c s hs i₃ c₃ hup T x y u z J hJ
  let φs : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left]
  let εs : Fin 2 → ℤ := ![1, -1]
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let A := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
    (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
    (LB.pullGen L.L φs εs s (b * d).left)
  have vA : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val A V.left z J = cubV c z J (V ≫ a)⁻¹ (V ≫ b)⁻¹ (V ≫ d)⁻¹ * val s ((V ≫ a) * (V ≫ b)).left z J *
        val s ((V ≫ a) * (V ≫ d)).left z J * val s ((V ≫ b) * (V ≫ d)).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
      (LB.pullGen L.L φs εs s (b * d).left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left) V.left
    have m3 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left) V.left
    refine m1.trans ?_
    rw [m2, m3, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul]
    rfl
  let B := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
    (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
    (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left)
  have vB : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val B V.left z J = cubV c z J (V ≫ a) (V ≫ b) (V ≫ d) * val s ((V ≫ a) * (V ≫ b) * (V ≫ d)).left z J *
        val s (V ≫ a).left z J * val s (V ≫ b).left z J * val s (V ≫ d).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left) V.left
    have m3 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left) V.left
    have m4 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left) V.left
    refine m1.trans ?_
    rw [m2, m3, m4, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ,
      val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, MonObj.comp_mul]
    rfl
  have hcorr : LB.Gen.Corr L.L _ _ _ _ A B := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB (cubeMapOf h).F3 i₃ (fun a b e => c₃ a b e) fun z J hJ => ?_
    let P : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
      lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
    have hP : (cubeMapOf h).F3 = P.left := rfl
    have ha : P ≫ a = pushHom h (G3 G') (x3 G' 0) := by simp [P, a, x3]; rfl
    have hb : P ≫ b = pushHom h (G3 G') (x3 G' 1) := by simp [P, b, x3]; rfl
    have hd : P ≫ d = pushHom h (G3 G') (x3 G' 2) := by simp [P, d, x3]; rfl
    rw [hP, vA _ P z J hJ, vB _ P z J hJ, ha, hb, hd]
    have e := hup (G3 G') z J hJ (x3 G' 0) (x3 G' 1) (x3 G' 2)
    simp only [map_inv, map_mul] at e ⊢
    exact e
  have e := val_corr hJ hcorr (lift x (lift y u)).left
  have ha : lift x (lift y u) ≫ a = x := by simp [a, x3]
  have hb : lift x (lift y u) ≫ b = y := by simp [b, x3]
  have hd : lift x (lift y u) ≫ d = u := by simp [d, x3]
  rw [vA _ _ z J hJ, vB _ _ z J hJ, ha, hb, hd] at e
  exact e

end GlobalTheory.CubeSymDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionLiftUnits
section
namespace GlobalTheory

theorem exists_even_cube_correction : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (U V : Type) [CommGroup U] [CommGroup V] (e : U →* V), Function.Injective e → ∀ a : X → V, (∀ x y w : X, ∃ u : U, a (x + y + w) * a x * a y * a w = e u * (a (x + y) * a (x + w) * a (y + w))) → (∀ x : X, ∃ u : U, a (-x) = e u * a x) → ∃ c : X → V, (∀ x y w : X, c (x + y + w) * c x * c y * c w = c (x + y) * c (x + w) * c (y + w)) ∧ (∀ x : X, c (-x) = c x) ∧ ∀ x : X, ∃ u : U, c x * a x = e u := by
  intro X _ _ _ U V _ _ e he a h3 hneg
  choose f hf using h3
  choose n hn using hneg
  have tA : ∀ {p q : V}, Additive.ofMul p = Additive.ofMul q → p = q := fun h => h
  have hfA : ∀ x y w, Additive.ofMul (a (x + y + w)) + Additive.ofMul (a x) + Additive.ofMul (a y)
      + Additive.ofMul (a w) = Additive.ofMul (e (f x y w)) + (Additive.ofMul (a (x + y))
      + Additive.ofMul (a (x + w)) + Additive.ofMul (a (y + w))) := fun x y w => by
    simpa only [ofMul_mul] using congrArg Additive.ofMul (hf x y w)
  have hnA : ∀ x, Additive.ofMul (a (-x)) = Additive.ofMul (e (n x)) + Additive.ofMul (a x) :=
    fun x => by simpa only [ofMul_mul] using congrArg Additive.ofMul (hn x)

  have hs1 : ∀ x y w, f x y w = f y x w := fun x y w => by
    apply he; apply tA
    have h1 := hfA x y w
    have h2 := hfA y x w
    rw [add_comm y x] at h2
    linear_combination (norm := module) h2 - h1
  have hs2 : ∀ x y w, f x y w = f x w y := fun x y w => by
    apply he; apply tA
    have h1 := hfA x y w
    have h2 := hfA x w y
    rw [add_right_comm x w y, add_comm w y] at h2
    linear_combination (norm := module) h2 - h1
  have hc : ∀ x x' x'' y, f (x + x') x'' y * f x x' y = f x (x' + x'') y * f x' x'' y := by
    intro x x' x'' y
    apply he; apply tA
    simp only [map_mul, ofMul_mul]
    have h1 := hfA (x + x') x'' y
    have h2 := hfA x x' y
    have h3 := hfA x (x' + x'') y
    have h4 := hfA x' x'' y
    rw [← add_assoc x x' x''] at h3
    linear_combination (norm := module) h3 + h4 - h1 - h2
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cubical_cocycle_isThirdDifference X U f hs1 hs2 hc
  have hgA : ∀ x y w, Additive.ofMul (e (f x y w)) + (Additive.ofMul (e (g (x + y)))
      + Additive.ofMul (e (g (x + w))) + Additive.ofMul (e (g (y + w))))
      = Additive.ofMul (e (g (x + y + w))) + Additive.ofMul (e (g x)) + Additive.ofMul (e (g y))
      + Additive.ofMul (e (g w)) := fun x y w => by
    simpa only [map_mul, ofMul_mul] using congrArg (fun v => Additive.ofMul (e v)) (hg x y w)

  obtain ⟨b, hb⟩ : ∃ b : X → V, ∀ x, b x = a x * (e (g x))⁻¹ := ⟨_, fun _ => rfl⟩
  have hbA : ∀ x, Additive.ofMul (b x) = Additive.ofMul (a x) - Additive.ofMul (e (g x)) :=
    fun x => by rw [hb, ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hΘb : ∀ x y w, Additive.ofMul (b (x + y + w)) + Additive.ofMul (b x) + Additive.ofMul (b y)
      + Additive.ofMul (b w) = Additive.ofMul (b (x + y)) + Additive.ofMul (b (x + w))
      + Additive.ofMul (b (y + w)) := fun x y w => by
    simp only [hbA]
    linear_combination (norm := module) hfA x y w + hgA x y w
  have hb0 : Additive.ofMul (b 0) = 0 := by
    have h0 := hΘb 0 0 0
    simp only [add_zero] at h0
    linear_combination (norm := module) h0

  have hε : ∀ x y, Additive.ofMul (b (-(x + y))) - Additive.ofMul (b (x + y))
      = (Additive.ofMul (b (-x)) - Additive.ofMul (b x))
        + (Additive.ofMul (b (-y)) - Additive.ofMul (b y)) := fun x y => by
    have t := hΘb x y (-(x + y))
    have e1 : x + y + -(x + y) = 0 := add_neg_cancel _
    have e2 : x + -(x + y) = -y := by abel
    have e3 : y + -(x + y) = -x := by abel
    rw [e1, e2, e3] at t
    linear_combination (norm := module) t - hb0
  obtain ⟨h, hh⟩ : ∃ h : X → U, ∀ x, h x = n x * g x * (g (-x))⁻¹ := ⟨_, fun _ => rfl⟩
  have heh : ∀ x, Additive.ofMul (e (h x)) = Additive.ofMul (b (-x)) - Additive.ofMul (b x) :=
    fun x => by
      rw [hh, e.map_mul, e.map_mul, e.map_inv, ofMul_mul, ofMul_mul, ofMul_inv, hbA, hbA]
      linear_combination (norm := module) -(hnA x)
  have hhom : ∀ x y, h (x + y) = h x * h y := fun x y => by
    apply he; apply tA
    rw [map_mul, ofMul_mul, heh, heh, heh, neg_add_rev, add_comm (-y) (-x)]
    have := hε x y
    rw [neg_add_rev, add_comm (-y) (-x)] at this
    exact this
  obtain ⟨k, hk3, hkneg⟩ := GlobalTheory.hom_eq_evenness_defect_of_cube X U h hhom
  refine ⟨fun x => e (k x) * (b x)⁻¹, ?_, ?_, ?_⟩
  · intro x y w
    apply tA
    simp only [ofMul_mul, ofMul_inv]
    have hk := congrArg (fun v => Additive.ofMul (e v)) (hk3 x y w)
    simp only [map_mul, ofMul_mul] at hk
    linear_combination (norm := module) hk - hΘb x y w
  · intro x
    apply tA
    simp only [ofMul_mul, ofMul_inv]
    have hk := congrArg (fun v => Additive.ofMul (e v)) (hkneg x)
    simp only [map_mul, ofMul_mul] at hk
    linear_combination (norm := module) hk + heh x
  · intro x
    refine ⟨k x * g x, ?_⟩
    apply tA
    simp only [ofMul_mul, ofMul_inv, map_mul, hbA]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
namespace PushCub
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β)

theorem push_one {T : Over S'} : pushHom h T 1 = toUnit _ ≫ η[G] := by
  rw [map_one, Hom.one_def]

theorem face0 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 0 =
    lift (pushHom h (G2 G') 1) (lift (pushHom h (G2 G') (fst G' G')) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face1 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 1 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') 1) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face2 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 2 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') (snd G' G')) (pushHom h (G2 G') 1)) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem pushPt_lift_cubeTriplePoint_of_isGrpPullback (i : Fin 3) : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫ x3 G i =
    pushHom h (G3 G') (x3 G' i) := by
  fin_cases i <;> simp [x3] <;> rfl

theorem pushPt_lift_cubeQuadruplePoint_of_isGrpPullback (i : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ x4 G i = pushHom h (G4 G') (x4 G' i) := by
  fin_cases i <;> simp [x4] <;> rfl

theorem padd_push (i j : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ padd G (x4 G i) (x4 G j) = pushHom h (G4 G') (x4 G' i * x4 G' j) := by
  rw [map_mul, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h i, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h j]
  exact MonObj.comp_mul _ _ _

theorem cubeMapOf_thirdFace_eq_pushPt_lift : (cubeMapOf h).F3 =
    (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left := rfl

theorem sw01 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 1) (lift (x3 G 0) (x3 G 2)) =
    lift (pushHom h (G3 G') (x3 G' 1)) (lift (pushHom h (G3 G') (x3 G' 0)) (pushHom h (G3 G') (x3 G' 2))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem sw12 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 0) (lift (x3 G 2) (x3 G 1)) =
    lift (pushHom h (G3 G') (x3 G' 0)) (lift (pushHom h (G3 G') (x3 G' 2)) (pushHom h (G3 G') (x3 G' 1))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem coc1 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0 * x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc2 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (x4 G 1) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

theorem coc3 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1 * x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc4 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 1) (lift (x4 G 2) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

end PushCub
end GlobalTheory.Mum

namespace GlobalTheory.Mum
open PushCub in

theorem cubicalStr_of_push_val : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  intro S S' G G' _ _ _ _ f β h L t ht i2 c2 i3 c3 i4 c4 hup
  have hv : ∀ {T : Over S'} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (V : Over.mk (T.hom ≫ f) ⟶ G3 G)
      (a b d : T ⟶ G'), V = lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d)) →
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t V.left z J =
        GlobalTheory.CubTransport.thV t z J (pushHom h T a) (pushHom h T b) (pushHom h T d) := by
    rintro T z J V a b d rfl; rfl
  refine ⟨{ t := t, isGen := ht, face := fun i => ?_, cubeSymmetric_swap_first := ?_, cubeSymmetric_swap_last := ?_, cocycle := ?_ }, rfl⟩
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i2 c2 fun z J hJ => ?_
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [← Over.comp_left]
    have C := hup (G2 G') z J hJ
    fin_cases i
    · exact (hv _ 1 (fst G' G') (snd G' G') (face0 h)).trans (C.face _ _)
    · exact (hv _ (fst G' G') 1 (snd G' G') (face1 h)).trans (C.face₂ _ _)
    · exact (hv _ (fst G' G') (snd G' G') 1 (face2 h)).trans (C.face₃ _ _)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s01 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 1) (x3 G' 0) (x3 G' 2) (sw01 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s12 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 0) (x3 G' 2) (x3 G' 1) (sw12 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i4 c4 fun z J hJ => ?_
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).symm)
    simp only [← Over.comp_left]
    have C := hup (G4 G') z J hJ
    exact (congrArg₂ (· * ·) (hv _ _ _ _ (coc1 h)) (hv _ _ _ _ (coc2 h))).trans ((C.coc _ _ _ _).trans
      (congrArg₂ (· * ·) (hv _ _ _ _ (coc3 h)) (hv _ _ _ _ (coc4 h))).symm)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamAlgebraQuotientRingSurjectiveAndKernelStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (G : Type) [CommRing G] [Algebra R G] (q : B →+* G) (h : SemiHom (RingHom.id R) q), Function.Surjective q → Function.Surjective h.m1 ∧ (∀ j, Function.Surjective (h.mOm j)) ∧ Function.Surjective h.mDR ∧ ∀ 𝔎 : Ideal (DR R B), (∀ x ∈ 𝔎, ∀ y, x * y ∈ 𝔎) → (∀ b, q b = 0 → algebraMap B (DR R B) b ∈ 𝔎 ∧ ι1 (D R B b) ∈ 𝔎) → ∀ x, h.mDR x = 0 → x ∈ 𝔎 := by
  first | exact @GlobalTheory.CechDR.semiHom_quotient_surjective_ker | exact GlobalTheory.CechDR.semiHom_quotient_surjective_ker | (intros; apply GlobalTheory.CechDR.semiHom_quotient_surjective_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamBasisBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.DRLine

theorem exists_basis_push_eq_sum : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p → ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ B : Module.Basis (Fin n) ℂ (HdR X.A), ∀ (a : orderC c) (α : X.A ⟶ X.A) [IsMonHom α],
      α.left ≫ p = p ≫ (cm.act a).left → ∀ i, push (dp0 ℂ) (𝟙 _) α (B i) =
        ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k := by
  intro hAb E _ _ _ c 𝔠 R X₀ X p cm hpull n eH
  have h : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hpull.grp
  have hm : (GlobalTheory.Published.AbelianDeRham.bcMor h).IsBC := (hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p h).1
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hAb.1 X₀.ab X₀.dim
  let b : Module.Basis (Fin n) R (HdR X₀.A) := Module.Basis.ofEquivFun eH
  let cb : Module.Basis (Fin n) R (primDR X₀.A) :=
    b.dualBasis.map (Module.evalEquiv R (primDR X₀.A)).symm
  have hcb : ∀ i j, b i (cb j) = if j = i then 1 else 0 := by
    intro i j
    simp [cb, Finsupp.single_apply, eq_comm]
  let L : ℂ ⊗[R] primDR X₀.A ≃ₗ[ℂ] primDR X.A := LinearEquiv.ofBijective _ hm
  let c' : Module.Basis (Fin n) ℂ (primDR X.A) := (Algebra.TensorProduct.basis ℂ cb).map L
  have hc' : ∀ j, c' j = (GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j) := fun j ↦ by
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact one_smul ℂ ((GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j))
  let B := c'.dualBasis
  have hB : ∀ i, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (b i) (B i) := by
    intro i x
    rw [← cb.sum_repr x]
    simp only [map_sum, map_smulₛₗ, ← hc', B, Module.Basis.dualBasis_apply_self, hcb, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> simp
  have hb : ∀ i, b i = eH.symm (Pi.single i 1) := fun i ↦ by simp [b]
  have hsum : ∀ v : Fin n → R, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (∑ k, v k • b k)
      (∑ k, ((v k : R) : ℂ) • B k) := by
    intro v x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hB _, map_sum, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hB k x]
    rfl
  refine ⟨B, fun a α _ hα i ↦ ?_⟩
  haveI := cm.hom a
  have e1 := GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor h) (cm.act a) α hα.symm (hB i)
  set v := (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) with hv
  have e2 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = ∑ k, v k • b k := by
    have e3 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = eH.symm v := by
      show act (dp0 R) (𝟙 _) cm a (b i) = _
      rw [hv, hb i]
      simp
    rw [e3, ← b.sum_equivFun (eH.symm v)]
    simp [b]
  rw [e2] at e1
  exact hm.unique e1 (hsum v)

end GlobalTheory.DRLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothConeStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_smooth_cone : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  first | exact @GlobalTheory.Poinc.MinSys.finite_minimiser_systems | exact GlobalTheory.Poinc.MinSys.finite_minimiser_systems | (intros; apply GlobalTheory.Poinc.MinSys.finite_minimiser_systems <;> assumption)
end

