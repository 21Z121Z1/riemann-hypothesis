import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnitStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  first | exact @GlobalTheory.Heat.liftDer_isDerivation | exact GlobalTheory.Heat.liftDer_isDerivation | (intros; apply GlobalTheory.Heat.liftDer_isDerivation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB → LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) → ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  first | exact @GlobalTheory.LBDescent.descCompat_of_lbIso | exact GlobalTheory.LBDescent.descCompat_of_lbIso | (intros; apply GlobalTheory.LBDescent.descCompat_of_lbIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def UT (N : Near π G) : Over (pullback π π) := Over.mk (pullback.snd N.U.hom (pullback.fst π π ≫ π))

def toS (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback N.U.hom π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [Category.assoc, hp]; exact pullback.condition)

def embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback G.hom p :=
  pullback.lift (toS N p hp ≫ N.u) (pullback.snd _ _) (by
    rw [Category.assoc, N.u_over, toS, pullback.lift_snd])

def emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⟶ (Over.pullback p).obj G :=
  Over.homMk (embL N p hp) (pullback.lift_snd _ _ _)

def sum [GrpObj G] (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⊗ UT N ⟶ (Over.pullback p).obj G :=
  (fst (UT N) (UT N) ≫ emb N p hp) * (snd (UT N) (UT N) ≫ emb N p hp)

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuotStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  first | exact @GlobalTheory.QuotDescent.descent | exact GlobalTheory.QuotDescent.descent | (intros; apply GlobalTheory.QuotDescent.descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpace
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.DivOn

theorem unitAt_of {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {u : Z.functionField} (h0 : u ≠ 0)
    (h : u ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range)
    (h' : u⁻¹ ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range) : UnitAt z u :=
  (unitAt_iff h0).2 ⟨h, h'⟩

theorem key {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) {gr : Root m → Y.Dv}
    {B : Mat m Y.Fn} (hB : B ∈ E'.S (genericPoint Y.X))
    (hgr : ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t)
    (W : Dbl Y) (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) {τ : ι} {a b : Fin (m τ)} (hab : (b : ℕ) = a + 1)
    (hC : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹)) {D₁ D₂ : Root m → CartierDiv W.Z}
    (hD₁ : ∀ x, IsPull W.p₁ (D₁ x) (gr x)) (hD₂ : ∀ x, IsPull W.p₂ (D₂ x) (gr x)) (z : W.Z)
    {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) :
    ∃ t₁ t₂ : Root m → W.Z.functionFieldˣ, (∀ x, (D₁ x).IsEqn z (t₁ x)) ∧ (∀ x, (D₂ x).IsEqn z (t₂ x)) ∧
      AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∧
      (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ →
        UnitAt z ((t₁ x : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) x.1 x.2 x.2 * t₂ x)) ∧
      UnitAt z ((t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (t₁ ⟨τ, b⟩ : W.Z.functionField)⁻¹ *
        minor τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) * (t₂ ⟨τ, a⟩ * t₂ ⟨τ, b⟩)) ∧
      (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b =
        (t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) τ a b * t₂ ⟨τ, b⟩ ∧
      RegAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨hP₁, h₁⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₁ hA₁
  obtain ⟨hP₂, h₂⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₂ hA₂
  choose s₁ e₁ q₁ using h₁
  choose s₂ e₂ q₂ using h₂
  have hT₁ : Par m ⊤ ((B * A₁⁻¹).map W.α₁) := hP₁.map W.α₁ fun _ _ => trivial
  have hT₂ : Par m ⊤ ((B * A₂⁻¹).map W.α₂) := hP₂.map W.α₂ fun _ _ => trivial
  have hloc := GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames F X Y ι m E E' φ f hf W hα z A₁ hA₁ A₂ hA₂
  have dB₁ : ∀ σ, (B.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dB₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dA₁ : ∀ σ, (A₁.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hA₁ σ)
  have eg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      ((B * A₁⁻¹).map W.α₁)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) * (B * A₂⁻¹).map W.α₂ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, Mat.mul_inv_rev, Mat.inv_inv dA₁, mul_assoc, mul_assoc,
      mul_assoc, ← mul_assoc (B.map W.α₂)⁻¹, Mat.inv_mul dB₂, one_mul, ← mul_assoc (B.map W.α₁)⁻¹, Mat.inv_mul dB₁,
      one_mul]
  obtain ⟨hal, hd, hab', hmin⟩ := GlobalTheory.T.minor_two_by_two_triangular_product ι m τ a b hab _ _ _ _ hT₁.inv hT₂ hC
  rw [← eg] at hal hd hab' hmin
  obtain ⟨hu, hm0, hm1⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ _ _ hal hloc
  have i₁ : ∀ x : Root m, ((B * A₁⁻¹).map W.α₁)⁻¹ x.1 x.2 x.2 = (W.α₁ (s₁ x))⁻¹ := fun x => by
    rw [(GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m _ ⊤ _ hT₁ x).2.2.1, ← e₁ x]; rfl
  have i₂ : ∀ x : Root m, ((B * A₂⁻¹).map W.α₂) x.1 x.2 x.2 = W.α₂ (s₂ x) := fun x => by
    rw [← e₂ x]; rfl
  refine ⟨fun x => Units.map W.α₁.toMonoidHom (s₁ x), fun x => Units.map W.α₂.toMonoidHom (s₂ x),
    fun x => hD₁ x _ _ (q₁ x) z rfl, fun x => hD₂ x _ _ (q₂ x) z rfl, hal, fun x hxa hxb => ?_, ?_, ?_,
    (hloc τ).1 a b⟩
  · have := unitAt_of (hu x hxa hxb).1 ((hloc x.1).1 x.2 x.2) (hu x hxa hxb).2
    rw [hd x hxa hxb, i₁, i₂] at this
    exact this
  · have hmem : minor τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∈
        (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range :=
      sub_mem (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _)) (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _))
    have := unitAt_of hm0 hmem hm1
    rw [hmin, i₁ ⟨τ, a⟩, i₁ ⟨τ, b⟩, i₂ ⟨τ, a⟩, i₂ ⟨τ, b⟩] at this
    exact this
  · rw [hab', i₁ ⟨τ, a⟩, i₂ ⟨τ, b⟩]
    rfl

theorem exists_divisors : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add, toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add, ← map_add, ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add, toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact GlobalTheory.T.not_isUnit_offDiagonal_transition_on_commonSection F X Y ι m E E' φ f hf W hα τ a b hne y A hA

end GlobalTheory.FlagPush.DivOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomainStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain : ∀ (A : CommRingCat.{0}) [IsDomain A], ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec A), (∀ x, (y x).asIdeal = ⊥) ∧ IsDominant y := by
  first | exact @GlobalTheory.exists_geomGeneric_dominant | exact GlobalTheory.exists_geomGeneric_dominant | (intros; apply GlobalTheory.exists_geomGeneric_dominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantTuplePrescribedMemberLinearForm
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc.DomTuple

section Squares

variable {X : Type} [AddCommGroup X]

def IsSumSq (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → X), ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → F β = ∑ i, β (x i) (x i)

theorem IsSumSq.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : IsSumSq G := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨ι, _, x, fun β hβ => (e β hβ).trans (hx β hβ)⟩

theorem IsSumSq.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (h' : IsSumSq G) :
    IsSumSq fun β => F β + G β := by
  obtain ⟨ι, _, x, hx⟩ := h
  obtain ⟨κ, _, y, hy⟩ := h'
  exact ⟨ι ⊕ κ, inferInstance, Sum.elim x y, fun β hβ => by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hx β hβ, hy β hβ]⟩

theorem IsSumSq.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (n : ℕ) : IsSumSq fun β => n * F β := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨Fin n × ι, inferInstance, fun p => x p.2, fun β hβ => by
    simp [Fintype.sum_prod_type, hx β hβ]⟩

theorem isSumSq_one (v : X) : IsSumSq fun β => β v v :=
  ⟨Unit, inferInstance, fun _ => v, fun β _ => by simp⟩

variable {m : ℕ} (a : Fin m → X)

def Absorbed (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ C : ℕ, IsSumSq fun β => C * ∑ i, β (a i) (a i) + F β

variable {a}

theorem Absorbed.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : Absorbed a G := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.congr fun β hβ => by rw [e β hβ]⟩

theorem Absorbed.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (h' : Absorbed a G) :
    Absorbed a fun β => F β + G β := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  exact ⟨C + C', (h.add h').congr fun β _ => by push_cast; ring⟩

theorem Absorbed.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (n : ℕ) : Absorbed a fun β => n * F β := by
  obtain ⟨C, h⟩ := h
  exact ⟨n * C, (h.nsmul n).congr fun β _ => by push_cast; ring⟩

theorem absorbed_sq (v : X) : Absorbed a fun β => β v v :=
  ⟨0, (isSumSq_one v).congr fun β _ => by simp⟩

theorem absorbed_zero : Absorbed a fun _ => 0 :=
  (absorbed_sq 0).congr fun β _ => by simp

theorem absorbed_sum {ι : Type} (S : Finset ι) (F : ι → LinearMap.BilinForm ℤ X → ℤ) (h : ∀ i, Absorbed a (F i)) :
    Absorbed a fun β => ∑ i ∈ S, F i β := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using absorbed_zero
  | insert i S hi ih => exact ((h i).add ih).congr fun β _ => Finset.sum_insert hi

theorem absorbed_neg_sq (ha : Submodule.span ℤ (Set.range a) = ⊤) (v : X) : Absorbed a fun β => - β v v := by
  have hv : v ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, {i // i ≠ j}, inferInstance, fun i => a i.1, fun β _ => ?_⟩
    have := Fintype.sum_eq_add_sum_subtype_ne (fun i => β (a i) (a i)) j
    simp only [Nat.cast_one, one_mul]
    rw [this]; ring
  | zero => exact absorbed_zero.congr fun β _ => by simp
  | add x y _ _ hx hy =>
    refine (((hx.nsmul 2).add (hy.nsmul 2)).add (absorbed_sq (x - y))).congr fun β _ => ?_
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    push_cast; ring
  | smul n x _ hx =>
    refine (hx.nsmul (n.natAbs ^ 2)).congr fun β _ => ?_
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    push_cast; rw [sq_abs]; ring

theorem absorbed_two_mul_apply (ha : Submodule.span ℤ (Set.range a) = ⊤) (u v : X) : Absorbed a fun β => 2 * β u v := by
  refine (((absorbed_sq (u + v)).add (absorbed_neg_sq ha u)).add (absorbed_neg_sq ha v)).congr fun β hβ => ?_
  simp only [map_add, LinearMap.add_apply, hβ v u]
  ring

theorem absorbed_two_mul [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Absorbed a fun β => 2 * F β := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β => by
    refine LinearMap.BilinForm.ext_basis b fun k l => ?_
    simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  refine (absorbed_sum Finset.univ _ fun i => absorbed_sum Finset.univ _ fun j =>
    absorbed_two_mul_apply ha (F (E i j) • b i) (b j)).congr fun β _ => ?_
  conv_lhs => rw [hE β]
  simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Squares

theorem exists_tuple {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} {a₀ : Fin m → X}
    (ha : Submodule.span ℤ (Set.range a₀) = ⊤) {s : ℕ} (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) {w : ℕ} (hw : 1 ≤ w)
    (hW : W 0 0 = w) (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (μ : Fin (s + 1) → X) (D₀ : ℕ) :
    ∃ (D l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), D₀ < D ∧ (∀ u, a (i₀, u) = μ u) ∧
      Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
        lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + (2 * w : ℕ) * lam β := by
  classical
  have h1 : Absorbed a₀ fun β => 2 * lam β + ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) :=
    (absorbed_two_mul ha lam).add (absorbed_sum _ _ fun u => absorbed_sum _ _ fun v => absorbed_two_mul_apply ha _ _)
  obtain ⟨C, ι, _, x, hx⟩ := h1
  let κ := Fin (2 * w) ⊕ (Fin (D₀ + 1) × Fin m) ⊕ ι
  let t : κ → Fin (s + 1) → X :=
    Sum.elim (fun _ => μ) (Sum.elim (fun p => Pi.single 0 (a₀ p.2)) fun i => Pi.single 0 (x i))
  let e := (Fintype.equivFin κ).symm
  refine ⟨w * (C + D₀ + 1), _, fun p => t (e p.1) p.2, e.symm (Sum.inl ⟨0, by omega⟩), by nlinarith, fun u => by simp [t],
    ?_, fun β hβ => ?_⟩
  · rw [eq_top_iff, ← ha]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨(e.symm (Sum.inr (Sum.inl (0, i))), 0), by simp [t]⟩
  · have hs : ∀ v : X, qW W β (Pi.single 0 v) = w * β v v := fun v => by
      simp [qW, Fin.sum_univ_succ, hW]
    have h2 : lin W (fun p : _ × _ => t (e p.1) p.2) β = ∑ k, qW W β (t k) := e.sum_comp fun k => qW W β (t k)
    have h3 := hx β hβ
    have h4 : ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) = -2 * qW W β μ := by
      simp only [qW, Finset.mul_sum, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [h4] at h3
    rw [h2]
    simp only [κ, t, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, hs, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← h3]
    push_cast; ring

theorem exists_dominant (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (hφ : IsPolFanOn bar φ X) (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a₀ : Fin m → X) (hγ : IsCone bar φ γ) (hne : NoEquivRays O γ) (hpos : ∀ x, x ≠ 0 → ∃ j, 0 < γ j x x)
    (hs : Supports bar φ d γ a₀) (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) (hW : PosW W) (N₁ : ℕ) (hN : 3 ≤ N₁)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hlam : ∀ j, 0 ≤ lam (γ j)) (μ : Fin (s + 1) → X) :
    ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧
      Dominant bar φ (D * d) N₁ W γ a ∧
      ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  have hW0 : 0 < W 0 0 := by
    have h : (0 : ℝ) < ((W + W.transpose).map (Int.cast : ℤ → ℝ)) 0 0 := Matrix.PosDef.diag_pos hW
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h
    omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ, W 0 0 = w := ⟨_, (Int.toNat_of_nonneg hW0.le).symm⟩
  have hw1 : 1 ≤ w := by omega
  let lam' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ((2 * w : ℕ) : ℤ) • lam
  have hlam' : ∀ j, 0 ≤ lam' (γ j) := fun j => mul_nonneg (Int.natCast_nonneg _) (hlam j)
  obtain ⟨D₀, hD₀⟩ := GlobalTheory.T.exists_supportingForm_gap_off_smoothCone O bar φ d X hφ r m γ a₀ hγ hs lam' hlam' (∑ j, lam' (γ j) + 1)
  obtain ⟨D, l, a, i₀, hD, hμ, hsp, hlin⟩ := exists_tuple hs.span W hw1 hw lam μ D₀
  obtain ⟨hle, hgap⟩ := hD₀ D hD.le
  have hlin' : ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + lam' β := fun β hβ => hlin β hβ.1
  have key : ∀ (e : X ≃ₗ[O] X) j, pull e.toLinearMap (γ j) = γ j ∨
      lin W a (γ j) < lin W (fun i => e (a i)) (γ j) := fun e j => by
    by_cases h : ∃ j', pull e.toLinearMap (γ j) = γ j'
    · obtain ⟨j', h⟩ := h
      exact Or.inl (hne e j j' h ▸ h)
    right
    have hc : IsCone bar φ ![pull e.toLinearMap (γ j)] := by
      have := (hφ.face _ 1 γ ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩ hγ).pull_equiv e
      have h0 : ![pull e.toLinearMap (γ j)] = fun _ : Fin 1 => pull e.toLinearMap (γ j) := funext fun i => by simp
      rw [h0]
      exact this
    have h1 := hgap _ hc fun j' hj => h ⟨j', hj⟩
    rw [← hlin' _ (pull_mem _ (hγ.mem j)), evalZ_pull φ (r := e.toLinearMap) e.surjective, mul_assoc, hs.eq j] at h1
    have h2 : D * ∑ i, γ j (a₀ i) (a₀ i) + (∑ j, lam' (γ j) + 1) ≤ lin W a (pull e.toLinearMap (γ j)) := by
      exact_mod_cast h1
    have h3 : lam' (γ j) ≤ ∑ j, lam' (γ j) := Finset.single_le_sum (fun j _ => hlam' j) (Finset.mem_univ j)
    change _ < lin W a (pull e.toLinearMap (γ j))
    rw [hlin' _ (hγ.mem j)]
    omega
  refine ⟨D, 2 * w, l, a, i₀, by omega, by omega, hμ, ⟨hsp, fun β hβ hp => ?_, fun e _ j => ?_, fun e he hx => ?_⟩,
    fun β hβ => hlin β hβ.1⟩
  · rw [hlin' β hβ, Nat.cast_mul]
    exact hle β hβ hp
  · rcases key e j with h | h
    · change _ ≤ lin W a (pull e.toLinearMap (γ j))
      rw [h]
    · exact h.le
  · by_contra hn
    have hfix : ∀ j, pull e.toLinearMap (γ j) = γ j := fun j => (key e j).resolve_right fun h => hn ⟨j, h⟩
    have := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ j, γ j) (fun x hx => by
      obtain ⟨j, hj⟩ := hpos x hx
      simp only [LinearMap.sum_apply]
      exact Finset.sum_pos' (fun i _ => hγ.nonneg i x) ⟨j, Finset.mem_univ j, hj⟩) e.toAddEquiv.toIntLinearEquiv
      (fun x y => by
        simp only [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hfix j) x y) N₁ hN he
    obtain ⟨x, hx⟩ := hx
    exact hx (LinearEquiv.congr_fun this x)

end GlobalTheory.Poinc.DomTuple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOneStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_over_height_one : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A] (𝔭 : PrimeSpectrum A), 𝔭.asIdeal.height = 1 → ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT := by
  first | exact @GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one | exact GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one | (intros; apply GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstantsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = E.formOrd (dForm c x) := by
  first | exact @GlobalTheory.FieldPair.placeEquiv_ringEquiv | exact GlobalTheory.FieldPair.placeEquiv_ringEquiv | (intros; apply GlobalTheory.FieldPair.placeEquiv_ringEquiv <;> assumption)
end

