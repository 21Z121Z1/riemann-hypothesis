import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0202

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionModelOfExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

private theorem exists_monoidHom_aut_of_lies {𝒞 : Type*} [Category 𝒞] {U X : 𝒞} (j : U ⟶ X)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).hom ≫ j)
    (lies : Γ → (X ⟶ X) → Prop) (h1 : lies 1 (𝟙 X)) (hrl : ∀ g, lies g (r g))
    (hml : ∀ g h, lies (g * h) (r h ≫ r g))
    (hj : ∀ g a b, lies g a → lies g b → j ≫ a = j ≫ b → a = b) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).hom = r g := by
  have hone : r 1 = 𝟙 X := by
    refine hj 1 _ _ (hrl 1) h1 ?_
    rw [hr 1, map_one, Category.comp_id]
    exact Category.id_comp j
  have hmul : ∀ g h, r (g * h) = r h ≫ r g := by
    intro g h
    refine hj (g * h) _ _ (hrl _) (hml g h) ?_
    have hm : ∀ a b : Aut U, (a * b).hom = b.hom ≫ a.hom := fun _ _ => rfl
    rw [hr (g * h), map_mul, hm, Category.assoc, reassoc_of% (hr h), hr g]
  have hinv : ∀ g, r g ≫ r g⁻¹ = 𝟙 X ∧ r g⁻¹ ≫ r g = 𝟙 X := fun g =>
    ⟨by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩
  exact ⟨{ toFun := fun g => ⟨r g, r g⁻¹, (hinv g).1, (hinv g).2⟩
           map_one' := Aut.ext hone
           map_mul' := fun g h => Aut.ext (hmul g h) }, fun g => rfl⟩

theorem exists_action_of_extends {U X : Scheme.{0}} (j : U ⟶ X) (hj : ∀ a b : X ⟶ X, j ≫ a = j ≫ b → a = b)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).hom ≫ j) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).hom = r g :=
  exists_monoidHom_aut_of_lies j ρ₀ r hr (fun _ _ => True) trivial (fun _ => trivial) (fun _ _ => trivial)
    (fun _ a b _ _ h => hj a b h)

theorem exists_action_model_of_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) {Z : Scheme.{0}}
    (q : C.X ⟶ Z) {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left)
    (ν : ∀ g, SABMap t t (ρ₀ g).hom) (hβ : IsDedFrac β) (hq : IsIntegralHom q) (hν : ∀ g, (ν g).φ = (τ₀ g).hom)
    (hZ : ∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).hom ≫ C.j ≫ q)
    (hext : ∀ (r : U ⟶ U) (n : SABMap t t r) (f : C.X ⟶ C.X), C.j ≫ f = r ≫ C.j →
      ∃ mu : SABMap C.t C.t f, C.m.φ ≫ mu.φ = n.φ ≫ C.m.φ) :
    ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom),
      ∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧
        C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have : IsFractionRing O F := hfr
  obtain ⟨hnoeth, _, hsep, hpre, hflat, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have := hnoeth
  have := hsep
  have : QuasiCompact C.j := hqc
  have : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨-, -, hsd, -⟩ := densePart_basic C.X U C.j hpre hflat hdom hqc
  have : IsSchemeTheoreticallyDominant C.j := hsd ‹_›
  have hj1 : ∀ a b : C.X ⟶ C.X, C.j ≫ a = C.j ≫ b → a = b := fun a b h =>
    ExtUnique.hom_ext_of_dominant (terminal.from C.X) (terminal.hom_ext _ _) C.j h
  have hlift : ∀ g, ∃ a : C.X ⟶ C.X, C.j ≫ a = (ρ₀ g).hom ≫ C.j := by
    intro g
    obtain ⟨ρZ, hρZ⟩ := hZ g
    obtain ⟨a, ⟨ha, -⟩, -⟩ := existsUnique_lift_of_densePart C.X U Z C.X C.j C.normal hpre hflat hdom hqc
      q (q ≫ ρZ) ((ρ₀ g).hom ≫ C.j) hq (by rw [Category.assoc, hρZ])
    exact ⟨a, ha⟩
  choose r hr using hlift
  obtain ⟨ρ, hρ⟩ := exists_action_of_extends C.j hj1 ρ₀ r hr
  have hjρ : ∀ g, C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j := fun g => by rw [hρ]; exact hr g
  have hmu : ∀ g, ∃ mu : SABMap C.t C.t (ρ g).hom, C.m.φ ≫ mu.φ = (ν g).φ ≫ C.m.φ :=
    fun g => hext _ (ν g) _ (hjρ g)
  choose mu hmu using hmu
  obtain ⟨hGf, hGs⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian C.t.G C.t.semi
  have := hGf
  have := hGs
  have hcan : ∀ (e : C.X ≅ C.X) (a b : C.t.G.left ⟶ C.t.G.left), a ≫ C.t.G.hom = C.t.G.hom ≫ e.hom →
      b ≫ C.t.G.hom = C.t.G.hom ≫ e.hom → C.m.φ ≫ a = C.m.φ ≫ b → a = b := by
    intro e a b ha hb hab
    have : IsSeparated (Over.mk (C.t.G.hom ≫ e.inv)).hom := by
      show IsSeparated (C.t.G.hom ≫ e.inv)
      infer_instance
    have key := ExtUnique.over_hom_ext_of_isPullback (j := C.j) (X := C.t.G)
      (Y := Over.mk (C.t.G.hom ≫ e.inv)) C.m.cart.1
      (f := Over.homMk a (by simp [reassoc_of% ha])) (g := Over.homMk b (by simp [reassoc_of% hb])) hab
    exact congrArg (fun k => k.left) key
  have hw : ∀ g, (mu g).φ ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).hom := fun g => (mu g).cart.1.w
  obtain ⟨τ, hτ⟩ := exists_monoidHom_aut_of_lies C.m.φ τ₀ (fun g => (mu g).φ)
    (fun g => by rw [hmu, hν]) (fun g a => a ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).hom)
    (by rw [map_one]; exact (Category.id_comp _).trans (Category.comp_id _).symm) hw
    (fun g h => by
      show ((mu h).φ ≫ (mu g).φ) ≫ C.t.G.hom = C.t.G.hom ≫ (ρ (g * h)).hom
      have hm : ∀ a b : Aut C.X, (a * b).hom = b.hom ≫ a.hom := fun _ _ => rfl
      rw [map_mul, hm, Category.assoc, hw g, reassoc_of% (hw h)])
    (fun g a b ha hb hab => hcan (ρ g) a b ha hb hab)
  refine ⟨ρ, τ, mu, fun g => ⟨(hτ g).symm, hjρ g, ?_⟩⟩
  rw [hτ]
  exact (hmu g).trans (by rw [hν])

theorem exists_action_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (C : Cpt c t β) (Z : Scheme.{0}) (q : C.X ⟶ Z) (Γ : Type) [Group Γ] [Finite Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ν : ∀ g, SABMap t t (ρ₀ g).hom), IsDedFrac β → Algebra.FiniteType ℤ O → IsProper t.G.hom → IsIntegralHom q → (∀ g, (ν g).φ = (τ₀ g).hom) → (∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).hom ≫ C.j ≫ q) → ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom), ∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧ C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ := by
  intro hN E _ _ _ H U F O _ _ c t β C Z q Γ _ _ ρ₀ τ₀ ν hβ hfin hprop hq hν hZ
  exact exists_action_model_of_ext C q ρ₀ τ₀ ν hβ hq hν hZ
    (fun r n f h => Models.exists_sabMap_extending hN E H U F O c t β U F O c t β C C r n f hβ hfin hprop h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodThetaObjectEmbeddingDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodThetaObjectEmbeddingData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  first | exact @GlobalTheory.ZM.GoodFibre.exists_fibData | exact GlobalTheory.ZM.GoodFibre.exists_fibData | (intros; apply GlobalTheory.ZM.GoodFibre.exists_fibData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_birational_models_ampleFrames : GlobalTheory.LN.HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (Z₁ Z₂ W : Scheme.{0}) (s₁ : Z₁ ⟶ Sp R) (s₂ : Z₂ ⟶ Sp R) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (tW : SAB H W) (j : W ⟶ Z₁) (j' : W ⟶ Z₂) (_ : SABMap tW t₁ j) (_ : SABMap tW t₂ j') (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsDedekindDomain R → CharZero R → Algebra.FiniteType ℤ R → IsNormalScheme Z₁ → IsProjOver s₁ → IsProjOver s₂ → Flat s₁ → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsProper tW.G.hom → j ≫ s₁ = j' ≫ s₂ → A₁.r = A₂.r → A₁.s = A₂.s → ∃ ρ : Z₁ ⟶ Z₂, j ≫ ρ = j' := by
  first | exact @GlobalTheory.AmpUniq.exists_hom_of_ampFrames | exact GlobalTheory.AmpUniq.exists_hom_of_ampFrames | (intros; apply GlobalTheory.AmpUniq.exists_hom_of_ampFrames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  first | exact @GlobalTheory.exists_polAV_of_veryDense_fibres | exact GlobalTheory.exists_polAV_of_veryDense_fibres | (intros; apply GlobalTheory.exists_polAV_of_veryDense_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  first | exact @GlobalTheory.exists_sab_glue_of_common_generic | exact GlobalTheory.exists_sab_glue_of_common_generic | (intros; apply GlobalTheory.exists_sab_glue_of_common_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianTripleMap_extending_modelMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by
  first | exact @GlobalTheory.Models.exists_sabMap_extending | exact GlobalTheory.Models.exists_sabMap_extending | (intros; apply GlobalTheory.Models.exists_sabMap_extending <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (s : Sp R ⟶ Sp o) (s' : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s) (t : TObj g (N' ^ 2) J b s') (v : Ix g (N' ^ 2) → R), TMap t t' (spMap (algebraMap R K)) → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g (N' ^ 2) J b s''), IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.HasTh (𝟙 _) (fun a => φ (v a)) ∧ t''.Shape Mat κ ∧ t''.Prim w w' := by
  first | exact @GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim | exact GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim | (intros; apply GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_thetaUnif : ThetaUnifAV → Out.Laws → N1c := fun hU hL =>
  GlobalTheory.familyUnif_of_parts GlobalTheory.datum_exists_period
    (GlobalTheory.PointUnif.exists_uniformisation_at_point_closed hU hL) (GlobalTheory.Moduli.exists_point_of_isPeriod hU hL) (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hU hL)
    (GlobalTheory.exists_local_period_lift hU hL) (GlobalTheory.T.isHolTo_modulipoint_exp_of_holomorphic_periods hU hL)
    (GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families GlobalTheory.SubfieldChart.exists_holomorphic_chart)
    (GlobalTheory.exists_thetaFrame_family hU hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  first | exact @GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | exact GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | (intros; apply GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

theorem Cpt.basic_of_isDedFrac (C : Cpt c t₀ β) (hβ : IsDedFrac β) :
    IsLocallyNoetherian C.X ∧ IsReduced C.X ∧ IsProper C.s ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j ∧ C.j ≫ C.s = c ≫ spMap β := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
  letI := β.toAlgebra
  obtain ⟨h1, -, -, h2, h3, h4, h5⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨h1, ?_, ?_, h2, h3, h4, h5, ?_⟩
  · have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  · obtain ⟨N, i, hi, e⟩ := C.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  · rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem Cpt.exists_extension_of_above (C : Cpt c t₀ β) (C' : Cpt c' t₀' β') (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r} (A : C'.Above C b r ν) (hb : IsFinite (spMap b))
    (hr : Surjective r) {R : Type} [CommRing R] {Z : Scheme.{0}} (sZ : Z ⟶ Sp R) (b' : R →+* O') (q : C'.X ⟶ Z)
    (hq : q ≫ sZ = C'.s ≫ spMap b') (hfin : IsFinite (pullback.lift q C'.s hq))
    (e : U ⟶ U) (e' : U' ⟶ U') (he : e ≫ c = c) (he' : e' ≫ c' = c') (hee : e' ≫ r = r ≫ e)
    (hqe : e' ≫ C'.j ≫ q = C'.j ≫ q) :
    ∃ ρ : C.X ⟶ C.X, ρ ≫ C.s = C.s ∧ C.j ≫ ρ = e ≫ C.j := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := C'.basic_of_isDedFrac hβ'
  obtain ⟨ρ', ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C'.X U' _ C'.X C'.j C'.normal m4 m5 m6 m7
    (pullback.lift q C'.s hq) (pullback.lift q C'.s hq) (e' ≫ C'.j) inferInstance (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, hqe]
      · simp only [Category.assoc, pullback.lift_snd, m8, reassoc_of% he'])
  have h3 : ρ' ≫ C'.s = C'.s := by
    have := congrArg (· ≫ pullback.snd sZ (spMap b')) h2
    simpa only [Category.assoc, pullback.lift_snd] using this
  have hπf : IsFinite A.π := by
    have h4 := A.fin
    have h5 : IsFinite (pullback.fst C.s (spMap b)) := inferInstance
    have h6 : A.π = pullback.lift A.π C'.s A.π_over ≫ pullback.fst C.s (spMap b) := (pullback.lift_fst _ _ _).symm
    rw [h6]; infer_instance
  have hπd : IsDominant A.π := by
    have : IsDominant (C'.j ≫ A.π) := by rw [A.j_comm]; infer_instance
    exact IsDominant.of_comp C'.j A.π
  have hπs : Surjective A.π := surjective_of_isDominant_of_isClosed_range A.π A.π.isClosedMap.isClosed_range
  obtain ⟨ρ, h7, h8⟩ := GlobalTheory.exists_desc_of_isFinite_of_densePart (Sp O) C'.X C.X U' U C.X A.π C'.j C.j r C.s C.s
    (ρ' ≫ A.π) (e ≫ C.j) C.normal m2 hπf hπs hr m6 m7 n4 n5 n6 n7 inferInstance inferInstance A.j_comm
    (by rw [reassoc_of% h1, A.j_comm, reassoc_of% hee])
    (by rw [Category.assoc, A.π_over, reassoc_of% h3])
    (by rw [Category.assoc, n8, reassoc_of% he])
  refine ⟨ρ, ext_of_isDominant C.j ?_, h7⟩
  rw [reassoc_of% h7, n8, reassoc_of% he]

end

theorem extendsAut_of_above : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  intro hext L1 L2 L3 E _ _ _ H D Xo n N T hpq l₀ l₁ h O₀ O₁ _ _ β₀ β₁ C C₁ b r ν A b' q hq hβ₀ hβ₁ hft hb hfin hjq
    hA hM hMb hcop hlev hr hk r₀ ν₀ g hr₀ hη
  obtain ⟨k, hk1, hk2, -⟩ := hk
  obtain ⟨r₁, ν₁, h1, h2, -, h4⟩ := GlobalTheory.T.exists_level_change_lift_keeping_etaA L1 L2 L3 E H D Xo hpq l₀ l₁ r ν r₀ ν₀ g hA hM hMb (h ▸ hcop) hlev
    ⟨k, hk1, hk2⟩ hr₀ hη
  have h5 : r₁.hom ≫ T.a l₁ h = T.a l₁ h := (T.compat l₁ l₁ h h r₁.hom ν₁ (RingHom.id _) (fun _ => rfl) (by
    rw [h1]
    exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id (CommRingCat.of (KA l₁))).symm)) h4).1
  obtain ⟨ρ, hρ1, hρ2⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.hom r₁.hom hr₀ h1 h2
    (by rw [hjq, h5])
  obtain ⟨ρ', hρ1', hρ2'⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.inv r₁.inv
    (by rw [Iso.inv_comp_eq, hr₀]) (by rw [Iso.inv_comp_eq, h1])
    (by rw [Iso.inv_comp_eq, reassoc_of% h2, Iso.hom_inv_id, Category.comp_id])
    (by rw [hjq, Iso.inv_comp_eq, h5])
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ₀
  let σ : C.X ≅ C.X :=
    { hom := ρ
      inv := ρ'
      hom_inv_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1', hρ1, Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2, hρ2', Iso.hom_inv_id_assoc, Category.comp_id])
      inv_hom_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1, hρ1', Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2', hρ2, Iso.inv_hom_id_assoc, Category.comp_id]) }
  obtain ⟨mu, hmu⟩ := exists_sabMap_extending hext E H _ _ _ _ _ β₀ _ _ _ _ _ β₀ C C r₀.hom ν₀ ρ hβ₀ hft
    (Xo l₀).univ.proper hρ2
  exact ⟨σ, mu, hρ1, hρ2, hmu⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cmModuli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.ZM.moduli_of_deeper_level | exact GlobalTheory.ZM.moduli_of_deeper_level | (intros; apply GlobalTheory.ZM.moduli_of_deeper_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_of_genericFibre_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (t : SAB H (Sp V)) (tK : SAB H (Sp K)) (_ : SABMap tK t (spMap (algebraMap V K))), IsProper t.G.hom → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre | exact GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre | (intros; apply GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre <;> assumption)
end

