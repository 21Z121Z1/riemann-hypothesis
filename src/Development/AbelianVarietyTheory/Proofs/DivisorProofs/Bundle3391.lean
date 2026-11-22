import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3372
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFibreProductAffineCompatibleStatement
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
theorem _root_.GlobalTheory.T.exists_derivation_fibreProduct_affine_compatible : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (O : Z.affineOpens) (hO : O.1 ≤ p ⁻¹ᵁ U.1) (δ : Derivation ℤ Γ(Z, O.1) Γ(Z, O.1)), (∀ r, δ ((p.appLE U.1 O.1 hO).hom r) = (p.appLE U.1 O.1 hO).hom (D r)) → ∃ δ' : Derivation ℤ Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1), (∀ r, δ' ((p'.appLE U'.1 _ inf_le_right).hom r) = (p'.appLE U'.1 _ inf_le_right).hom (D' r)) ∧ ∀ f, δ' ((φ.appLE O.1 _ inf_le_left).hom f) = (φ.appLE O.1 _ inf_le_left).hom (δ f) := by
  first | exact @GlobalTheory.FibreDer.exists_der_fibre | exact GlobalTheory.FibreDer.exists_der_fibre | (intros; apply GlobalTheory.FibreDer.exists_der_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorField
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenDer

open GlobalTheory.Points

theorem top_le_preimage_of_mem {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (y : Sp A ⟶ X)
    (V : X.Opens) (h : y (IsLocalRing.closedPoint A) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro z _
  exact (IsLocalRing.specializes_closedPoint z).mem_open (y ⁻¹ᵁ V).isOpen h

theorem germ_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (p : X) (hp : p ∈ V) (f : Γ(X, U)) :
    X.presheaf.germ V p hp (resG X h f) = X.presheaf.germ U p (h hp) f :=
  X.presheaf.germ_res_apply (homOfLE h) p hp f

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem eventually_zero {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X)
    (hx : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) (O : X.Opens) (f : Γ(X, O))
    (hO : ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O)
    (hf : valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f = 0) :
    ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O' ∧ resG X h f = 0 := by
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  set p := ξ (IsLocalRing.closedPoint (FractionRing Ω)) with hp
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (show x (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := top_le_preimage_of_mem x U hqU
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_comp (V := ⊤) _ x hxU (le_preimage_top _)
  have hpU : p ∈ U := hξU (Set.mem_univ _)
  have hpO : p ∈ O := hO (Set.mem_univ _)
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hpU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk p) (hU.primeIdealOf ⟨p, hpU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨p, hpU⟩
  obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl
    (X.presheaf.germ O p hpO f)
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk p) a s
  have hmk' : IsLocalization.mk' (X.presheaf.stalk p) a s = X.presheaf.germ O p hpO f := hmk
  rw [hmk'] at hspec
  have halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk p) r = X.presheaf.germ U p hpU r := fun _ => rfl
  rw [halg, halg] at hspec
  have hsu : IsUnit (X.presheaf.germ U p hpU (s : Γ(X, U))) := by
    rw [← halg]; exact IsLocalization.map_units _ s
  have hps : p ∈ X.basicOpen (s : Γ(X, U)) := (X.mem_basicOpen (s : Γ(X, U)) p hpU).mpr hsu
  have hg : X.presheaf.germ (O ⊓ U) p (show p ∈ O ⊓ U from ⟨hpO, hpU⟩) (resG X inf_le_left f * resG X inf_le_right (s : Γ(X, U))) =
      X.presheaf.germ U p hpU a := by
    rw [map_mul, germ_resG, germ_resG, hspec]
  obtain ⟨W₁, hpW₁, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq X.presheaf p (show p ∈ O ⊓ U from ⟨hpO, hpU⟩) hpU _ _ hg
  have e1 : X.presheaf.map iU.op = X.presheaf.map (homOfLE (leOfHom iU)).op := rfl
  have e2 : X.presheaf.map iV.op = X.presheaf.map (homOfLE (leOfHom iV)).op := rfl
  rw [e1, e2] at heq
  change resG X (leOfHom iU) _ = resG X (leOfHom iV) a at heq
  have hξW₁ : ⊤ ≤ ξ ⁻¹ᵁ W₁ := top_le_preimage_of_mem ξ W₁ hpW₁
  have hval := congrArg (valR ξ W₁) heq
  rw [valR_res ξ _ hξW₁, valR_res ξ _ hξW₁, valR_mul ξ _ (le_preimage_mono ξ (leOfHom iU) hξW₁),
    valR_res ξ _ (le_preimage_mono ξ (leOfHom iU) hξW₁), hf, zero_mul, hξ, valR_spMap_comp _ x U hxU] at hval
  have ha0 : a = 0 := hx U a hxU ((IsFractionRing.injective Ω (FractionRing Ω)) (by rw [← hval, map_zero]))
  rw [ha0, map_zero, map_mul, resG_resG, resG_resG] at heq
  set O₃ : X.Opens := W₁ ⊓ X.basicOpen (s : Γ(X, U)) with hO₃
  have h₃ : O₃ ≤ W₁ := inf_le_left
  have hunit : IsUnit (resG X (h₃.trans ((leOfHom iU).trans inf_le_right)) (s : Γ(X, U))) := by
    have h0 : IsUnit (resG X (X.basicOpen_le (s : Γ(X, U))) (s : Γ(X, U))) :=
      RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace (s : Γ(X, U))
    rw [← resG_resG (X.basicOpen_le (s : Γ(X, U))) (show O₃ ≤ X.basicOpen (s : Γ(X, U)) from inf_le_right)]
    exact h0.map _
  refine ⟨O₃, h₃.trans ((leOfHom iU).trans inf_le_left), top_le_preimage_of_mem ξ O₃ (show p ∈ O₃ from ⟨hpW₁, hps⟩), ?_⟩
  have := congrArg (resG X h₃) heq
  rw [map_mul, resG_resG, resG_resG, map_zero] at this
  exact (hunit.mul_left_eq_zero).mp this

theorem valR_sub {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq x U h, map_sub]

theorem top_le_preimage_inf {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) {U V : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun _ hz => ⟨hU hz, hV hz⟩

section Field

variable {X : Scheme.{0}} {K : Type} [Field K] (ξ : Sp K ⟶ X) (W : X.Opens)

def valField (hW : ⊤ ≤ ξ ⁻¹ᵁ W) : Subfield K where
  carrier := {y | ∃ (O : X.Opens) (f : Γ(X, O)), O ≤ W ∧ ⊤ ≤ ξ ⁻¹ᵁ O ∧ valR ξ O f = y}
  zero_mem' := ⟨W, 0, le_rfl, hW, valR_zero ξ W hW⟩
  one_mem' := ⟨W, 1, le_rfl, hW, valR_one ξ W hW⟩
  add_mem' := by
    rintro _ _ ⟨O, f, hOW, hO, rfl⟩ ⟨O', f', -, hO', rfl⟩
    have h2 := top_le_preimage_inf ξ hO hO'
    refine ⟨O ⊓ O', resG X inf_le_left f + resG X inf_le_right f', inf_le_left.trans hOW, h2, ?_⟩
    rw [valR_add ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2]
  mul_mem' := by
    rintro _ _ ⟨O, f, hOW, hO, rfl⟩ ⟨O', f', -, hO', rfl⟩
    have h2 := top_le_preimage_inf ξ hO hO'
    refine ⟨O ⊓ O', resG X inf_le_left f * resG X inf_le_right f', inf_le_left.trans hOW, h2, ?_⟩
    rw [valR_mul ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2]
  neg_mem' := by
    rintro _ ⟨O, f, hOW, hO, rfl⟩
    exact ⟨O, -f, hOW, hO, valR_neg ξ O hO f⟩
  inv_mem' := by
    rintro _ ⟨O, f, hOW, hO, rfl⟩
    by_cases h0 : valR ξ O f = 0
    · rw [h0, inv_zero]; exact ⟨W, 0, le_rfl, hW, valR_zero ξ W hW⟩
    · have hB := (le_preimage_basicOpen_iff ξ hO f).mpr (Ne.isUnit h0)
      have hfu : IsUnit (resG X (X.basicOpen_le f) f) :=
        RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace f
      obtain ⟨u, hu⟩ := hfu
      refine ⟨X.basicOpen f, ↑u⁻¹, (X.basicOpen_le f).trans hOW, hB, ?_⟩
      have : valR ξ (X.basicOpen f) (↑u⁻¹) * valR ξ O f = 1 := by
        rw [← valR_res ξ (X.basicOpen_le f) hB f, ← valR_mul ξ _ hB]
        change valR ξ (X.basicOpen f) (↑u⁻¹ * resG X (X.basicOpen_le f) f) = 1
        rw [← hu, Units.inv_mul, valR_one ξ _ hB]
      exact eq_inv_of_mul_eq_one_left this

variable {ξ W}

theorem valR_der_eq (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (d : Fld X) (hd : IsField W d) {O O' : X.Opens} (f : Γ(X, O)) (f' : Γ(X, O')) (hOW : O ≤ W) (hO'W : O' ≤ W)
    (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (hO' : ⊤ ≤ ξ ⁻¹ᵁ O') (e : valR ξ O f = valR ξ O' f') :
    valR ξ O (d O f) = valR ξ O' (d O' f') := by
  have h2 := top_le_preimage_inf ξ hO hO'
  obtain ⟨O₃, h₃, hO₃, hz⟩ := H (O ⊓ O') (resG X inf_le_left f - resG X inf_le_right f') h2
    (by rw [valR_sub ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2, e, sub_self])
  rw [map_sub, resG_resG, resG_resG, sub_eq_zero] at hz
  rw [← valR_res ξ (h₃.trans inf_le_left) hO₃, ← valR_res ξ (h₃.trans inf_le_right) hO₃,
    ← hd.2.2 O O₃ _ hOW f, ← hd.2.2 O' O₃ _ hO'W f', hz]

end Field

section Der

variable {X : Scheme.{0}} {K : Type} [Field K] (ξ : Sp K ⟶ X) (W : X.Opens)

theorem mem_valField_iff (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (y : K) :
    y ∈ valField ξ W hW ↔ ∃ (O : X.Opens) (f : Γ(X, O)), O ≤ W ∧ ⊤ ≤ ξ ⁻¹ᵁ O ∧ valR ξ O f = y := Iff.rfl

def valDer (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (y : valField ξ W hW) : K :=
  valR ξ (Classical.choose ((mem_valField_iff ξ W hW y).mp y.2))
    (d _ (Classical.choose (Classical.choose_spec ((mem_valField_iff ξ W hW y).mp y.2))))

variable {ξ W}

theorem valDer_eq (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (y : valField ξ W hW) {O : X.Opens} (f : Γ(X, O))
    (hOW : O ≤ W) (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (e : valR ξ O f = y) : valDer ξ W hW d y = valR ξ O (d O f) := by
  obtain ⟨hOW', hO', e'⟩ := Classical.choose_spec (Classical.choose_spec ((mem_valField_iff ξ W hW y).mp y.2))
  exact valR_der_eq H d hd _ f hOW' hOW hO' hO (e'.trans e.symm)

theorem valDer_add (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (a b : valField ξ W hW) :
    valDer ξ W hW d (a + b) = valDer ξ W hW d a + valDer ξ W hW d b := by
  obtain ⟨O, f, hOW, hO, ea⟩ := (mem_valField_iff ξ W hW a).mp a.2
  obtain ⟨O', f', hO'W, hO', eb⟩ := (mem_valField_iff ξ W hW b).mp b.2
  have h2 := top_le_preimage_inf ξ hO hO'
  have h2W : O ⊓ O' ≤ W := inf_le_left.trans hOW
  rw [valDer_eq H hW d hd (a + b) (resG X inf_le_left f + resG X inf_le_right f') h2W h2
      (by rw [valR_add ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2, ea, eb]; rfl),
    valDer_eq H hW d hd a (resG X (inf_le_left : O ⊓ O' ≤ O) f) h2W h2 (by rw [valR_res ξ _ h2, ea]),
    valDer_eq H hW d hd b (resG X (inf_le_right : O ⊓ O' ≤ O') f') h2W h2 (by rw [valR_res ξ _ h2, eb]),
    hd.1 _ h2W, valR_add ξ _ h2]

theorem valDer_mul (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (a b : valField ξ W hW) :
    valDer ξ W hW d (a * b) = (a : K) * valDer ξ W hW d b + (b : K) * valDer ξ W hW d a := by
  obtain ⟨O, f, hOW, hO, ea⟩ := (mem_valField_iff ξ W hW a).mp a.2
  obtain ⟨O', f', hO'W, hO', eb⟩ := (mem_valField_iff ξ W hW b).mp b.2
  have h2 := top_le_preimage_inf ξ hO hO'
  have h2W : O ⊓ O' ≤ W := inf_le_left.trans hOW
  have ea' : valR ξ (O ⊓ O') (resG X inf_le_left f) = a := by rw [valR_res ξ _ h2, ea]
  have eb' : valR ξ (O ⊓ O') (resG X inf_le_right f') = b := by rw [valR_res ξ _ h2, eb]
  rw [valDer_eq H hW d hd (a * b) (resG X inf_le_left f * resG X inf_le_right f') h2W h2
      (by rw [valR_mul ξ _ h2, ea', eb']; rfl),
    valDer_eq H hW d hd a (resG X (inf_le_left : O ⊓ O' ≤ O) f) h2W h2 ea',
    valDer_eq H hW d hd b (resG X (inf_le_right : O ⊓ O' ≤ O') f') h2W h2 eb',
    hd.2.1 _ h2W, valR_add ξ _ h2, valR_mul ξ _ h2, valR_mul ξ _ h2, ea', eb']

end Der

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem exists_derivation_fractionRing : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] [CharZero Ω] (x : Sp Ω ⟶ X), (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) → ∀ (W : X.Opens) (d : Fld X), IsField W d → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ W → ∃ dt0 : Derivation ℤ (FractionRing Ω) (FractionRing Ω), ∀ (O : X.Opens) (f : Γ(X, O)), O ≤ W → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (d O f) = dt0 (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ _ x hx W d hd hW
  set K := FractionRing Ω
  set ξ := spMap (algebraMap Ω K) ≫ x with hξ
  have H := eventually_zero x hx
  set F := valField ξ W hW
  haveI : CharZero K := ⟨fun m n h => by
    rw [← map_natCast (algebraMap Ω K) m, ← map_natCast (algebraMap Ω K) n] at h
    exact Nat.cast_injective (IsFractionRing.injective Ω K h)⟩
  haveI : CharZero F := ⟨fun m n h => Nat.cast_injective (R := K) (by simpa using congrArg Subtype.val h)⟩
  haveI : Algebra.FormallySmooth F K := formallySmooth_of_charZero F K
  obtain ⟨d', hadd, hmul, hext⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth F K K (RingHom.id K)
    (valDer ξ W hW d) (valDer_add H hW d hd) (fun a b => valDer_mul H hW d hd a b)
  refine ⟨{ toFun := d'
            map_add' := hadd
            map_smul' := ?_
            map_one_eq_zero' := ?_
            leibniz' := ?_ }, fun O f hOW hO => ?_⟩
  · intro m y
    have := (AddMonoidHom.mk' d' hadd).map_zsmul m y
    simp only [AddMonoidHom.mk'_apply, zsmul_eq_mul] at this
    simp only [RingHom.id_apply, Algebra.smul_def, algebraMap_int_eq, eq_intCast, smul_eq_mul]
    rw [this]; simp
  · have h1 := hmul 1 1
    simp only [RingHom.id_apply, _root_.one_mul, _root_.mul_one] at h1
    show d' 1 = 0
    linear_combination -h1
  · intro a b
    show d' (a * b) = a • d' b + b • d' a
    simp [hmul, smul_eq_mul]
  have hmem : valR ξ O f ∈ F := ⟨O, f, hOW, hO, rfl⟩
  change _ = d' (algebraMap F K ⟨_, hmem⟩)
  rw [hext]
  exact (valDer_eq H hW d hd ⟨_, hmem⟩ f hOW hO rfl).symm

end GlobalTheory.GenDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffineStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  first | exact @GlobalTheory.LiftDer.exists_lift_preimage | exact GlobalTheory.LiftDer.exists_lift_preimage | (intros; apply GlobalTheory.LiftDer.exists_lift_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivSec
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

theorem exists_div_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s a b : LB.Sec (LB.LinComb L φ ε)) (U : Y.Opens) (f : Γ(Y, U))
    (hs : ∀ z ∈ U, ∀ J, Good L z J → IsUnit (sval s (𝟙 Y) z J)) :
    ∃ g : Γ(Y, U), ∀ z ∈ U, ∀ J, Good L z J →
      sval a (𝟙 Y) z J = gs (𝟙 Y) z U f * sval b (𝟙 Y) z J + gs (𝟙 Y) z U g * sval s (𝟙 Y) z J := by
  have hun : ∀ (j : K → L.ι) (y : Y), y ∈ U → y ∈ LB.wchart L φ j →
      IsUnit (gs (𝟙 Y) y (LB.wchart L φ j) (s.f j)) := fun j y hU hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    rw [e]
    exact (Units.isUnit _).mul (hs y hU J hJ)
  let W : (K → L.ι) → Y.Opens := fun j => U ⊓ LB.wchart L φ j
  have hloc : ∀ j, ∃ u : Γ(Y, W j), ∀ y ∈ W j,
      gs (𝟙 Y) y (LB.wchart L φ j) (a.f j) = gs (𝟙 Y) y U f * gs (𝟙 Y) y (LB.wchart L φ j) (b.f j) +
        gs (𝟙 Y) y (W j) u * gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) := by
    intro j
    have l₁ : W j ≤ U := inf_le_left
    have l₂ : W j ≤ LB.wchart L φ j := inf_le_right
    have hu : IsUnit ((Y.presheaf.map (homOfLE l₂).op).hom (s.f j)) :=
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 Y) y (W j) hy _).symm.trans (gs_res (𝟙 Y) y l₂ hy (s.f j)))).mpr
          (hun j y hy.1 hy.2)
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have key : (Y.presheaf.map (homOfLE l₂).op).hom (a.f j) =
        (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j) +
        (((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v) *
          (Y.presheaf.map (homOfLE l₂).op).hom (s.f j) := by
      rw [_root_.mul_assoc, hv]; ring
    refine ⟨((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v, fun y hy => ?_⟩
    refine (gs_res (𝟙 Y) y l₂ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (W j)) key).trans ?_)
    refine (gs_add (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y l₁ hy _) (gs_res (𝟙 Y) y l₂ hy _))
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg _ (gs_res (𝟙 Y) y l₂ hy _))
  choose u hu using hloc
  obtain ⟨g, hg, -⟩ := Y.sheaf.existsUnique_gluing' W U (fun j => homOfLE inf_le_left) (fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => I (φ k), hy, Set.mem_iInter.2 fun k => hI _⟩) u
    (fun j j' => fn_ext (V := W j ⊓ W j') fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      have e₁ := hu j y hy.1
      have e₂ := hu j' y hy.2
      rw [sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, sec_trans b (𝟙 Y) y hy.1.2 hy.2.2,
        sec_trans s (𝟙 Y) y hy.1.2 hy.2.2] at e₁
      have hc := (Units.isUnit (trF φ ε (𝟙 Y) y j j')).mul (hun j' y hy.1.1 hy.2.2)
      refine hc.mul_right_cancel ?_
      linear_combination (trF φ ε (𝟙 Y) y j j').val * e₂ - e₁)
  refine ⟨g, fun z hz J hJ => ?_⟩
  have hm : z ∈ W (fun k => J (𝟙 Y ≫ φ k)) := ⟨hz, hJ.mem φ (𝟙 Y)⟩
  have e : gs (𝟙 Y) z U g = gs (𝟙 Y) z (W _) (u (fun k => J (𝟙 Y ≫ φ k))) :=
    (gs_res (𝟙 Y) z inf_le_left hm g).symm.trans (congrArg (gs (𝟙 Y) z (W _)) (hg _))
  rw [e]
  exact hu _ z hm

theorem exists_isRem : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (α : Q.X) (σ σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ g : Γ(Q.P.A.left, U), GlobalTheory.HeatRatio.IsRem Q σ' σp σp' U f g := by
  intro R _ _ Q N α σ σ' σp σp' U f h
  exact exists_div_sec Q.P.isLB σ' σp σp' U f fun z hz J hJ => (h z hz J hJ).1

end GlobalTheory.HeatRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteBasisTangentModuleSmoothCommGroupSch
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBasis

theorem exists_basis_tanM : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  intro R _ _ G _ _ hG
  exact GlobalTheory.RayBasis.exists_basis hG

end GlobalTheory.TanBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupSchemeStatement
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
theorem _root_.GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  first | exact @GlobalTheory.FormalOrigin.exists_formalPoint | exact GlobalTheory.FormalOrigin.exists_formalPoint | (intros; apply GlobalTheory.FormalOrigin.exists_formalPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionFieldMapBasicOpenFormalPoint
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem fracIotaBasicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left), x' ≫ t.G.hom = spMap φ → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∃ iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω), ∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r) := by
  intro E _ _ _ H R _ _ t c hc Ω _ _ φ x' hx hinj
  have e1 : ∀ y : Γ(Sp R, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
      ((x'.appTop).hom ((t.G.hom.appTop).hom y)) = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    intro y
    have n := congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    rw [← n, show Spec.map (CommRingCat.ofHom φ) = x' ≫ t.G.hom from hx.symm, Scheme.Hom.comp_appTop]
    rfl
  have e2 : ∀ y : Γ(Sp R, ⊤), ((η[t.G]).left.appTop).hom ((t.G.hom.appTop).hom y) = y := by
    intro y
    have w : (η[t.G]).left ≫ t.G.hom = 𝟙 (Sp R) := by simpa using Over.w η[t.G]
    have := congrArg (fun k => (Scheme.Hom.appTop k).hom y) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : t.G.left.Opens) := by simp
  have inj : ∀ r : R, φ r = 0 → r = 0 := by
    intro r hr
    set y := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r with hy
    have hv : valR x' ⊤ ((t.G.hom.appTop).hom y) = 0 := by
      unfold valR
      rw [dif_pos ht]
      have : x'.appLE ⊤ ⊤ ht = x'.appTop := Scheme.Hom.appLE_eq_app _
      rw [this, e1, hy]
      simpa using hr
    have h0 := hinj ⊤ _ ht hv
    have h1 := e2 y
    rw [h0, map_zero] at h1
    have : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y = r := by simp [hy]
    rw [← this, ← h1, map_zero]
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing Ω :=
    (algebraMap Ω (FractionRing Ω)).comp (φ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, s, RingHom.comp_apply]
    have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) = c := by simp
    rw [hs]
    intro h0
    exact hc (inj c ((IsFractionRing.injective Ω (FractionRing Ω)) (by simpa using h0)))
  refine ⟨IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu, fun r => ?_⟩
  show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
    (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
  rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  simp [gg]

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heatOperator_glued_pullbackBundlePower : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) → ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  first | exact @GlobalTheory.Heat.Glue.exists_acts | exact GlobalTheory.Heat.Glue.exists_acts | (intros; apply GlobalTheory.Heat.Glue.exists_acts <;> assumption)
end

