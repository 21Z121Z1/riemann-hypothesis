import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinrankQuotientSpanModEqOne
section
open Polynomial

namespace GlobalTheory

theorem isLocalization_fractionRing_of_finite_polynomial (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] [Module.Finite k[X] A] [FaithfulSMul k[X] A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) (FractionRing A) := by
  have hinj : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X]) ≤ nonZeroDivisors A := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  refine
    { map_units := fun y => IsLocalization.map_units (FractionRing A) ⟨y.1, hle y.2⟩
      surj := fun z => ?_
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective A (FractionRing A) hxy]⟩ }
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := k[X]) hb0 (Ideal.mem_span_singleton_self (b : A))
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨p, hpI, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpI
  refine ⟨⟨c * a, ⟨_, ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩⟩⟩, ?_⟩
  simp only
  rw [← hc, map_mul, map_mul, ← hab]
  ring

end GlobalTheory

namespace GlobalTheory

theorem exists_finrank_quotient_span_mod_eq_one :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A]
      [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N →
      ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  intro k A _ _ _ _ _ _ _ _ _ N hN
  have : FaithfulSMul k[X] A := inferInstance
  have hinjA : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  set L := FractionRing A
  have hinjL : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] A L]
    exact (IsFractionRing.injective A L).comp hinjA
  have : FaithfulSMul k[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjL
  letI : Algebra (RatFunc k) L := RatFunc.liftAlgebra k L
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) L :=
    isLocalization_fractionRing_of_finite_polynomial k A
  have : Module.Finite (RatFunc k) L :=
    Module.Finite.of_isLocalization k[X] A (Rₚ := RatFunc k) (Sₚ := L) (nonZeroDivisors k[X])
  have hC1 : GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) :=
    GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) (RatFunc k) (GlobalTheory.tsenLang_ratFunc k)
  obtain ⟨h, hh⟩ := GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) L hC1 RatFunc.X RatFunc.X_ne_zero
  obtain ⟨⟨x, ⟨_, ⟨m, hm0, rfl⟩⟩⟩, hx⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) h
  have hm0' : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set g : A := x * algebraMap k[X] A (m ^ M) with hg
  have hgL : algebraMap A L g
      = h * algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (m ^ (M + 1))) := by
    simp only at hx
    rw [hg, map_mul, ← hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, pow_succ, map_mul]
    ring
  have hnorm : Algebra.norm k[X] g = X * (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [← Algebra.norm_localization k[X] (Rₘ := RatFunc k) (Sₘ := L) (nonZeroDivisors k[X]) g, hgL, map_mul, hh,
      Algebra.norm_algebraMap, map_mul, RatFunc.algebraMap_X, ← map_pow]
  have hp : (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hm0')
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hnorm
    exact mul_ne_zero X_ne_zero hp hnorm.symm
  refine ⟨g, hg0, ?_⟩
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hnorm,
    natDegree_mul X_ne_zero hp, natDegree_X, natDegree_pow, natDegree_pow, mul_left_comm,
    Nat.add_mul_mod_self_left]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCover
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem glue_upward_of_cov : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Glue (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H hdir t Sg hup hcov s hs
  have key : ∀ (t₁ t₂ : C') (a₁ : t ⟶ t₁) (a₂ : t ⟶ t₂), Sg t₁ a₁ → Sg t₂ a₂ → ∀ (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ a₁) = mp F w₂ (s t₂ a₂) := by
    intro t₁ t₂ a₁ a₂ h₁ h₂ S w₁ w₂
    refine sub_eq_zero.1 (Basis.eq_zero_of_local F G H hdir ⟨w₁⟩ ⟨w₂⟩ _
      fun t₃ S' ψ ⟨b₁⟩ ⟨b₂⟩ ⟨g⟩ ↦ ?_)
    have e1 : mp F ψ (mp F w₁ (s t₁ a₁)) = mp F g (s t₃ (a₁ ≫ b₁)) := by
      rw [hs t₁ t₃ a₁ b₁ h₁, ← mp_comp]
      change _ = mp F g (mp F (G.map b₁) _)
      rw [← mp_comp F (G.map b₁) g, Subsingleton.elim (G.map b₁ ≫ g) (w₁ ≫ ψ)]
    have e2 : mp F ψ (mp F w₂ (s t₂ a₂)) = mp F g (s t₃ (a₂ ≫ b₂)) := by
      rw [hs t₂ t₃ a₂ b₂ h₂, ← mp_comp]
      change _ = mp F g (mp F (G.map b₂) _)
      rw [← mp_comp F (G.map b₂) g, Subsingleton.elim (G.map b₂ ≫ g) (w₂ ≫ ψ)]
    have e3 : a₁ ≫ b₁ = a₂ ≫ b₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov
  have hex : ∀ S (u : G.obj t ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t' : C') (a : t ⟶ t') (w : G.obj t' ⟶ S), Sg t' a ∧ mp F w (s t' a) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t', a, ha, ⟨w⟩⟩ := hb' i S u hi
      exact ⟨mp F w (s t' a), fun _ ↦ ⟨t', a, w, ha, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t₁, a₁, w₁, h₁, e₁⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi.map _
    obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
    rw [← e₁, ← e₂, ← mp_comp]
    exact key _ _ _ _ h₂ h₁ _ _ _
  refine ⟨x, fun t' a ha ↦ ?_⟩
  change mp F (G.map a) x = s t' a
  refine sub_eq_zero.1 (sep_std H (Basis.span_map_eq_top F (G.map a) hb) _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (G.map a ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (G.map a ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e₂, key t₂ t' a₂ a h₂ ha S' w₂ ψ, sub_self]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace PullUnifHom

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff' x L f i).1 (le_left' h)
  have hj := (chart_pull_iff' x L f j).1 (le_right' h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

theorem exists_holUnif_pull_hom : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro A B _ _ φ L g u' ex Λ Hm χ' hadd honto hker hdisc hfull hhol hφ hΛ hAH
  have keyl : ∀ z, (ex z).left ≫ φ.left = (u'.ex z).left := fun z => by rw [← Over.comp_left, hφ]
  have hch : ∀ (j : (L.pull φ.left).ι) z, (⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔
      ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  let u : HolUnif A (L.pull φ.left) g :=
    ⟨ex, hadd, honto, Λ, hker, hdisc, hfull, hhol, fun j z => u'.fr (j PUnit.unit) z,
     fun j => (u'.fr_hol (j PUnit.unit)).mono (fun z hz => (hch j z).1 hz),
     fun j z hz => u'.fr_ne _ _ ((hch j z).1 hz),
     fun i j z h => by
        have hi := (hch i z).1 (le_left' h)
        have hj := (hch j z).1 (le_right' h)
        show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
        rw [valAt'_pull_g' _ L _ i j h, keyl z]
        exact u'.fr_compat _ _ _ (inf_of _ hi hj)⟩
  refine ⟨u, fun l => χ' ⟨l.1, hΛ l.2⟩, fun w => Iff.rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hAH
  exact ⟨h1, h2, fun l => h3 _, fun l i z hz => h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((hch i z).1 hz)⟩

end PullUnifHom
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagQuadraticSubfieldOfToricCMFieldData
section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped IntermediateField

namespace GlobalTheory.QuadInHost

theorem exists_quadField : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  intro E _ _ I _ d φ hF hd4 Λ hΛ
  obtain ⟨hp, hd, -, -, -, hI, -, w, hw, hφw⟩ := hF
  have hd0 : (0 : ℚ) < d := by exact_mod_cast hp.pos
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval w (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ) = 0 := by
    simp [hw]
  have hi : IsIntegral ℚ w := ⟨_, hm, he⟩
  have h2 : Module.finrank ℚ ℚ⟮w⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ w hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have h1 : (algebraMap ℚ E q) ^ 2 = -(d : E) := by rw [hq]; exact hw
    have h3 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ E).injective (by simpa using h1)
    nlinarith [sq_nonneg q]
  let r : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hr : r ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [r] using hw)
  let φK : ℚ⟮w⟯ →+* ℂ := (φ i₀).comp (algebraMap ℚ⟮w⟯ E)
  have hφr : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) r = Complex.I * (Real.sqrt d : ℂ) := fun i => hφw i
  have hsq : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
    exact_mod_cast this.ne'
  refine ⟨ℚ⟮w⟯, h2, GlobalTheory.discr_eq_neg_of_sq_eq h2 hp.squarefree hd4 hr, φK, ?_, ?_, ?_⟩
  · intro i
    have := (IntermediateField.adjoin.powerBasis hi).algHom_ext
      (f := ((φ i).comp (algebraMap ℚ⟮w⟯ E)).toRatAlgHom) (g := φK.toRatAlgHom)
      (by simp only [IntermediateField.adjoin.powerBasis_gen]; exact (hφr i).trans (hφr i₀).symm)
    exact congrArg AlgHom.toRingHom this
  · intro h
    have := congrArg (fun f => f r) h
    simp only [RingHom.comp_apply] at this
    change starRingEnd ℂ (φK r) = φK r at this
    rw [show φK r = _ from hφr i₀] at this
    simp [Complex.conj_ofReal] at this
    have h0 : (2 * Complex.I) * (Real.sqrt d : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h0 with h0 | h0
    · simp at h0
    · exact hsq h0
  · obtain ⟨ω, hω2, hgen⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 hp.squarefree hd4 hr
    have hφω : φK ω = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
      have := congrArg φK hω2
      rw [map_mul, map_add, map_one, map_ofNat, show φK r = _ from hφr i₀] at this
      linear_combination this / 2
    unfold IsLatOf
    ext x
    rw [SetLike.mem_coe, hΛ x]
    constructor
    · rintro ⟨hx, a, b, rfl⟩
      let y : ℚ⟮w⟯ := a + b * r
      have hy : φK y = a + b * (Complex.I * (Real.sqrt d : ℂ)) := by
        simp only [y, map_add, map_mul, map_ratCast, show φK r = _ from hφr i₀]
      have hint : IsIntegral ℤ y := by
        rw [← hy] at hx
        exact (isIntegral_algHom_iff φK.toIntAlgHom φK.injective).1 hx
      refine ⟨y, ?_, hy⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨⟨y, hint⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff] at hy
      obtain ⟨c, rfl⟩ := hy
      refine ⟨(RingOfIntegers.isIntegral_coe c).map φK.toIntAlgHom, ?_⟩
      obtain ⟨m, n, rfl⟩ := hgen c
      refine ⟨m + n / 2, n / 2, ?_⟩
      change φK ((m + n * ω : 𝓞 ℚ⟮w⟯) : ℚ⟮w⟯) = _
      push_cast
      simp only [map_add, map_mul, hφω]
      simp
      ring

end GlobalTheory.QuadInHost
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddNsmul
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.UCls.NormOneMod

theorem exists_integer_add_nsmul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (M : ℕ) (hM : 1 ≤ M) (k : RA F E) (hk : k ∈ hat1 F {x : E | IsIntegral ℤ x}) :
    ∃ x : 𝓞 E, ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + M • y := by
  induction hk using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨u, b, hb, h⟩ := (strong_approximation_mod_nat F M hM).2 a ha
    have hu : IsIntegral ℤ (algebraMap F E (u : F)) := u.isIntegral_coe.algebraMap
    refine ⟨⟨algebraMap F E (u : F) * x, hu.mul hx⟩, b ⊗ₜ x, tmul_mem_adelicCompletion_of_integral F hb hx, ?_⟩
    rw [h, TensorProduct.add_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    obtain ⟨x', y', hy', rfl⟩ := h2
    refine ⟨x + x', y + y', add_mem hy hy', ?_⟩
    have : ((x + x' : 𝓞 E) : E) = x + x' := by simp
    rw [this, TensorProduct.tmul_add, smul_add]
    abel
  | neg y _ h1 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    refine ⟨-x, -y, neg_mem hy, ?_⟩
    have : ((-x : 𝓞 E) : E) = -x := by simp
    rw [this, TensorProduct.tmul_neg, smul_neg]
    abel

theorem exists_reps (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M) :
    ∃ T : Finset (𝓞 E), T.card ≤ M ^ Module.finrank ℚ E ∧
      ∀ x : 𝓞 E, ∃ t ∈ T, ∃ y : 𝓞 E, x = t + M • y := by
  classical
  let b := Module.finBasis ℤ (𝓞 E)
  let g : (Fin (Module.finrank ℤ (𝓞 E)) → Fin M) → 𝓞 E := fun f => ∑ i, ((f i : ℕ) : ℤ) • b i
  refine ⟨Finset.univ.image g, ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp [RingOfIntegers.rank]
  · have hM0 : (0 : ℤ) < M := by exact_mod_cast hM
    let f : Fin (Module.finrank ℤ (𝓞 E)) → Fin M := fun i =>
      ⟨(b.repr x i % M).toNat, by
        have h1 := Int.emod_nonneg (b.repr x i) hM0.ne'
        have h2 := Int.emod_lt_of_pos (b.repr x i) hM0
        omega⟩
    refine ⟨g f, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ∑ i, (b.repr x i / M) • b i, ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    simp only [g, f, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne'), ← natCast_zsmul, smul_smul, ← add_smul,
      Int.emod_add_mul_ediv]

theorem two_mul_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    2 * fdeg E = Module.finrank ℚ E := by
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [h2] at h
  unfold fdeg
  omega

theorem exists_reps_normOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (M : ℕ) (hM : 1 ≤ M) :
    ∃ S : Finset (RA F E), S.card ≤ M ^ Module.finrank ℚ E ∧ ∀ k : RA F E, IsTA c k →
      k ∈ hat1 F {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA c s ∧ ∃ k', IsTA c k' ∧
        (∃ y ∈ hat1 F {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  classical
  obtain ⟨T, hT, hT'⟩ := exists_reps E M hM
  let P : 𝓞 E → RA F E → Prop := fun t k => IsTA c k ∧ k ∈ hat1 F {x : E | IsIntegral ℤ x} ∧
    ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E) + M • y
  let s : 𝓞 E → RA F E := fun t => Classical.epsilon (P t)
  refine ⟨T.image s, Finset.card_image_le.trans hT, fun k hk hk' => ?_⟩
  obtain ⟨x, y, hy, hxy⟩ := exists_integer_add_nsmul F E M hM k hk'
  obtain ⟨t, ht, z, rfl⟩ := hT' x
  have hP : P t k := by
    refine ⟨hk, hk', (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (z : E) + y,
      add_mem (one_tmul_mem_adelicCompletionOfElementSet F z.isIntegral_coe) hy, ?_⟩
    have : ((t + M • z : 𝓞 E) : E) = t + M • (z : E) := by simp
    rw [hxy, this, TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, add_assoc]
  obtain ⟨hs, hs', w, hw, hsw⟩ : P t (s t) := Classical.epsilon_spec ⟨k, hP⟩
  obtain ⟨-, -, w', hw', hkw⟩ := hP
  have hc : sg (FiniteAdeleRing (𝓞 F) F) c (s t) ∈ hat1 F {x : E | IsIntegral ℤ x} :=
    galoisAut_mem_adelicCompletionOfElementSet F c (fun x hx => IsIntegral.map (c : E →+* E).toIntAlgHom hx) hs'
  refine ⟨s t, Finset.mem_image_of_mem _ ht, hs, k * sg _ c (s t), ?_,
    ⟨(w' - w) * sg _ c (s t), mul_mem_adelicCompletionOfElementSet_of_mul_mem F (fun a ha b hb => IsIntegral.mul ha hb)
      (sub_mem hw' hw) hc, ?_⟩, ?_⟩
  · have h1 := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) hs
    rw [map_mul, map_one] at h1
    unfold IsTA at hk ⊢
    rw [map_mul, mul_mul_mul_comm, hk, h1, one_mul]
  · have h1 : k - s t = M • (w' - w) := by
      rw [smul_sub]
      conv_lhs => rw [hkw, hsw]
      abel
    unfold IsTA at hs
    rw [← smul_mul_assoc, ← h1, sub_mul, hs]
  · unfold IsTA at hs
    rw [mul_left_comm, hs, mul_one]

theorem normOne_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ), 1 ≤ M → ∃ S : Finset (RA (maximalRealSubfield E) E), S.card ≤ M ^ (2 * fdeg E) ∧ ∀ k : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) k → k ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA (IsCMField.complexConj E) s ∧ ∃ k', IsTA (IsCMField.complexConj E) k' ∧ (∃ y ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  intro E _ _ _ M hM
  rw [two_mul_fdeg]
  exact exists_reps_normOne _ E _ M hM

end GlobalTheory.UCls.NormOneMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfTraceDualElement
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

theorem traceDual_integral_of_not_dvd_discr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by
  intro E _ _ _ l hl hd O _ _ _ _ K _ _ _ hlm σ y hy

  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨x, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨k, hk⟩ := hy x
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, hk]
    simp
  have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
    rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hint0 := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hmem
  rw [← coe_discr, Algebra.smul_def, mul_one] at hint0
  have hint : IsIntegral ℤ ((NumberField.discr E : E) * y) := by simpa using hint0

  have hσ : IsIntegral ℤ (σ ((NumberField.discr E : E) * y)) := hint.map σ.toIntAlgHom
  have hO : IsIntegral O (σ ((NumberField.discr E : E) * y)) := hσ.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hO

  have hcop : IsCoprime (l : ℤ) (NumberField.discr E) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit ((NumberField.discr E : ℤ) : O) := by
    by_contra hn
    have hdm : ((NumberField.discr E : ℤ) : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hlm' : ((l : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by simpa using hlm
    have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : ((a : O) * ((l : ℤ) : O) + (b : O) * ((NumberField.discr E : ℤ) : O)) = 1 := by
        exact_mod_cast congrArg (Int.cast (R := O)) hab
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm') (Ideal.mul_mem_left _ _ hdm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : Oˣ) * z, ?_⟩
  rw [map_mul, hz, map_mul, map_intCast, ← map_intCast (algebraMap O K), ← hu', ← mul_assoc,
    ← map_mul, Units.inv_mul, map_one, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiMap_of_tensorPairing : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K', ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  first | (exact @GlobalTheory.EtC.semiMap_of_tensorPair) | (exact GlobalTheory.EtC.semiMap_of_tensorPair) | (intros; apply GlobalTheory.EtC.semiMap_of_tensorPair  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHomStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  first | (exact @GlobalTheory.EtC.twist_mul_map) | (exact GlobalTheory.EtC.twist_mul_map) | (intros; apply GlobalTheory.EtC.twist_mul_map  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentatiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q)) (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) = Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) → extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  first | (exact @GlobalTheory.EtC.extAug_comp_ext) | (exact GlobalTheory.EtC.extAug_comp_ext) | (intros; apply GlobalTheory.EtC.extAug_comp_ext  <;> assumption)
end

