import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalPolChartsKS
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3353
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_modification_ks_iso : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  first | exact @GlobalTheory.LogCanonicalReflexive.logCanon_refl | exact GlobalTheory.LogCanonicalReflexive.logCanon_refl | (intros; apply GlobalTheory.LogCanonicalReflexive.logCanon_refl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
section
namespace GlobalTheory.ChernDegree

theorem chernWeilNumbers_holds : GlobalTheory.Published.ChernWeilNumbers :=
  GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral GlobalTheory.T.degree_eq_integral_topChernForm_complex

end GlobalTheory.ChernDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePolynomialDefectBilinearAdditiveParts
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

namespace GlobalTheory

theorem cocycle_polynomial_defect : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  intro R X _ _ _ _ w π π' h
  have key : ∀ k : ℕ, 1 ≤ k → ∀ mu mu' α : X,
      2 * (k : R) * (w (mu + mu') α - w mu α - w mu' α)
        + 2 * (k : R) ^ 2 * (π (mu + mu') - π mu - π mu' - w mu' mu)
        + 2 * (k : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
    intro k hk mu mu' α
    have e := h k hk mu mu' α
    simp only [map_add, map_nsmul, nsmul_eq_mul] at e
    linear_combination e
  have hAB : ∀ mu mu' : X, π (mu + mu') - π mu - π mu' - w mu' mu = 0 ∧
      π' (mu + mu') - π' mu - π' mu' = 0 := by
    intro mu mu'
    have h1 := key 1 le_rfl mu mu' 0
    have h2 := key 2 (by norm_num) mu mu' 0
    simp only [map_zero] at h1 h2
    push_cast at h1 h2
    have h4 : (4 : R) * (π (mu + mu') - π mu - π mu' - w mu' mu) = 0 := by
      linear_combination h2 - 2 * h1
    have hA : π (mu + mu') - π mu - π mu' - w mu' mu = 0 :=
      (mul_eq_zero.mp h4).resolve_left (by norm_num)
    refine ⟨hA, ?_⟩
    have h2' : (2 : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
      linear_combination h1 - 2 * hA
    exact (mul_eq_zero.mp h2').resolve_left (by norm_num)
  have hw : ∀ mu mu' α : X, w (mu + mu') α = w mu α + w mu' α := by
    intro mu mu' α
    have e := key 1 le_rfl mu mu' α
    obtain ⟨hA, hB⟩ := hAB mu mu'
    push_cast at e
    have e2 : (2 : R) * (w (mu + mu') α - w mu α - w mu' α) = 0 := by
      linear_combination e - 2 * hA - 2 * hB
    have := (mul_eq_zero.mp e2).resolve_left (by norm_num)
    linear_combination this
  refine ⟨hw, ?_, ?_, ?_⟩
  · intro mu mu'
    have a := (hAB mu mu').1
    have b := (hAB mu' mu).1
    rw [add_comm mu' mu] at b
    linear_combination a - b
  · intro mu mu'
    linear_combination (hAB mu mu').2
  · intro mu mu'
    linear_combination (hAB mu mu').1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdjPolLocal
open GlobalTheory.MulPull GlobalTheory.PrimNorm GlobalTheory.PrimNormPol

theorem commGroup_sixTerm_relation_to_zpow_form {G : Type} [CommGroup G] {p q r s t u o : G}
    (h : p * q⁻¹ * r⁻¹ * o = s * t⁻¹ * u⁻¹ * o) :
    p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) = 1 := by
  have h' := mul_right_cancel h
  have e : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) =
      (p * q⁻¹ * r⁻¹) * (s * t⁻¹ * u⁻¹)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  rw [e, h', mul_inv_cancel]

theorem commGroup_sixTerm_zpow_form_to_relation {G : Type} [CommGroup G] {p q r s t u o : G}
    (h : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) = 1) :
    p * q⁻¹ * r⁻¹ * o = s * t⁻¹ * u⁻¹ * o := by
  congr 1
  have e : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) =
      (p * q⁻¹ * r⁻¹) * (s * t⁻¹ * u⁻¹)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  rw [e, mul_inv_eq_one] at h
  exact h

theorem le_val_one_add_pow_sub {G : Type} [CommGroup G] {D a b : G} (h : 1 = D * (1 * a⁻¹ * b⁻¹ * 1)) : D = a * b := by
  rw [_root_.one_mul, _root_.mul_one, eq_comm, ← mul_inv, mul_inv_eq_one] at h
  exact h

theorem lbIso_of_rosatiAdj_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → RosatiAdj B M f g → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
  intro R _ _ B _ _ M f g hM h
  obtain ⟨U, hU, t, ht⟩ := h (closedPoint R)
  have hall : ∀ p : Sp R, p ∈ U := fun p =>
    Specializes.mem_open ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1
      (le_maximalIdeal p.2.ne_top)) U.isOpen hU
  have H : KerPow.HasGen M (rosatiφ B f g) rosatiε :=
    KerPow.HasGen.of_range (W := (B ⊗ B).hom ⁻¹ᵁ U) ⟨t, ht⟩ (𝟙 _) (fun y => hall _) (fun k => Category.id_comp _)
  have h6 := (hasGen_iff hM _ _).1 H
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, rosatiφ, rosatiε] at h6
  have ea : (padd B (fst B B ≫ f) (snd B B)).left = ((fst B B ≫ f) * snd B B).left := rfl
  have eb : (padd B (fst B B) (snd B B ≫ g)).left = (fst B B * (snd B B ≫ g)).left := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, ea, eb, _root_.mul_one] at h6
  refine (lbIso_iff hM _ _ _ _).2 ?_
  rw [prod_square_id, prod_square_id]
  simp only [diff₂]
  exact commGroup_sixTerm_zpow_form_to_relation h6

theorem rosatiAdj_of_lbIso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) → RosatiAdj B M f g := by
  intro S B _ _ M f g hM h
  have h1 := (lbIso_iff hM _ _ _ _).1 h
  rw [prod_square_id, prod_square_id] at h1
  have H : KerPow.HasGen M (rosatiφ B f g) rosatiε := by
    refine (hasGen_iff hM _ _).2 ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, rosatiφ, rosatiε]
    simp only [diff₂] at h1
    have ea : (padd B (fst B B ≫ f) (snd B B)).left = ((fst B B ≫ f) * snd B B).left := rfl
    have eb : (padd B (fst B B) (snd B B ≫ g)).left = (fst B B * (snd B B ≫ g)).left := rfl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, ea, eb, _root_.mul_one]
    exact commGroup_sixTerm_relation_to_zpow_form h1
  intro s
  exact ⟨⊤, trivial, H.pull ((B ⊗ B).hom ⁻¹ᵁ ⊤).ι fun _ => rfl⟩

end GlobalTheory.AdjPolLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreFinitelyGeneratedExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue | exact GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue | (intros; apply GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem crystallineCechDeRhamComparison_bijective_complexAbelian :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  intro A _ hA
  have := hA.smooth
  have := hA.proper
  exact GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne (str A)
    inferInstance inferInstance inferInstance

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CrysFlatBC

open GlobalTheory.SmoothLift

theorem bijective_liftSemi_pull1 : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  intro R D _ _ _ _ π κ hκ hπ X s t φ hs hs' hs'' ht hφ m
  subst hφ ht
  obtain ⟨e₁, e₂, -, -, n⟩ := (GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations : GlobalTheory.Published.CrystallineSmoothLift)
  have hb : spMap π ≫ spMap (algebraMap R D) = 𝟙 _ := by
    rw [← Cris.spMap_comp, show π.comp (algebraMap R D) = RingHom.id R from RingHom.ext hπ, Cris.spMap_id]
  obtain ⟨X', q, s', H⟩ : ∃ (X' : Scheme.{0}) (q : X' ⟶ X) (s' : X' ⟶ Sp D),
      IsPullback q s' s (spMap (algebraMap R D)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let i : X ⟶ X' := H.lift (𝟙 X) (s ≫ spMap π) (by rw [Category.assoc, hb]; simp)
  have hiq : i ≫ q = 𝟙 X := H.lift_fst _ _ _
  have his : i ≫ s' = s ≫ spMap π := H.lift_snd _ _ _
  have hp : IsPullback i s s' (spMap π) :=
    IsPullback.of_right (by rw [hiq, hb]; exact IsPullback.id_horiz s) his H
  have k1 : Smooth s' := MorphismProperty.of_isPullback (P := @Smooth) H hs
  have k2 : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) H hs'
  have k3 : QuasiCompact s' := MorphismProperty.of_isPullback (P := @QuasiCompact) H hs''
  let D₀ := Data.self s hs hs' hs''
  let D' := Data.ofQuot κ hκ π (fun a ↦ ⟨_, hπ a⟩) rfl s' s i k1 k2 k3 hp _ rfl
  have w : 𝟙 X ≫ 𝟙 X = i ≫ q := by rw [hiq, Category.id_comp]
  have key := (n D₀ D' (algebraMap R D) q (𝟙 X) H.w m w).1
  obtain ⟨e, e', he⟩ : ∃ (e : Cris.H1 (dp0 R) s ≃ₗ[R] HH1 s) (e' : Cris.H1 κ (s ≫ spMap π) ≃ₗ[D] HH1 s'),
      ∀ c, IsPull1 H.w (e c) (e' (m.pull1 c)) := ⟨e₁ D₀, e₁ D', key⟩
  exact (GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ R D (Cris.H1 (dp0 R) s) (HH1 s) (Cris.H1 κ (s ≫ spMap π)) (HH1 s')
    e.toLinearMap e'.toLinearMap m.pull1 (pullHH1 H.w) e.bijective e'.bijective fun c ↦ (he c).eq_pullHH1).2
    (GlobalTheory.T.hyper_cohomology_flat_base_change R D X X' s s' q H hs' hs'')

end GlobalTheory.CrysFlatBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem toH1O_surjective_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  intro hH R _ A _ g hab hdim
  rw [Category.comp_id]
  have hsm : Smooth A.hom := hab.smooth
  have hsep : IsSeparated A.hom := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact A.hom := by haveI := hab.proper; infer_instance
  have hcmp := GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne A.hom hsm hsep hqc
  have hsurj : Function.Surjective (GlobalTheory.CechDR.toHO1 A.hom) := (hH R A g hab hdim).2.2.2.2.1.2.2
  intro u
  obtain ⟨h, hh⟩ := hsurj (GlobalTheory.CechDR.cmpO A.hom u)
  obtain ⟨c, rfl⟩ := hcmp.2 h
  refine ⟨c, GlobalTheory.CechDR.cmpO_injective R A.left A.hom ?_⟩
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, hh]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIso
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

noncomputable section

namespace GlobalTheory.StalkDer

theorem derivation_extend_stalk_of_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  intro X X' f _ U d x hx
  have hU' : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let φ : Γ(X, U.1) ≃+* Γ(X', f ⁻¹ᵁ U.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
  letI : Algebra Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) :=
    X'.presheaf.algebra_section_stalk (⟨x, hx⟩ : f ⁻¹ᵁ U.1)
  haveI := hU'.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ a, algebraMap Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) a =
      (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom a := fun a => rfl
  let g : Γ(X', f ⁻¹ᵁ U.1) →+ X'.presheaf.stalk x :=
    (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.toAddMonoidHom.comp
      (φ.toRingHom.toAddMonoidHom.comp (d.toLinearMap.toAddMonoidHom.comp φ.symm.toRingHom.toAddMonoidHom))
  have hg : ∀ a, g a = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom (φ (d (φ.symm a))) := fun a => rfl
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x)
    (hU'.primeIdealOf ⟨x, hx⟩).asIdeal
    (intDerivationOfLeibniz g (fun a b => by
      simp only [hg, map_mul, Derivation.leibniz, smul_eq_mul, map_add, Algebra.smul_def, halg,
        RingEquiv.apply_symm_apply]))
  refine ⟨D', fun r => ?_⟩
  have h1 := hD' (φ r)
  rw [halg] at h1
  refine h1.trans ?_
  show g (φ r) = _
  rw [hg, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.StalkDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Theory

theorem frobProj_omega_surjective {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (G : PDivGroup p k) : Function.Surjective (frobProj (p_eq_zero p k) G).omega := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  intro t
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G k (p_eq_zero p k)).2 t
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩
  | tmul r w =>
    refine ⟨(frobeniusEquiv k p).symm r • w, ?_⟩
    rw [liftSemi_tmul, map_smulₛₗ]
    congr 1
    show frobRing (p_eq_zero p k) _ = r
    rw [frobRing_apply, frobeniusEquiv_symm_pow_p]

theorem hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  intro p _ T k _ _ _ G
  obtain ⟨-, hVinj, hVsm, -, -⟩ := GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
  obtain ⟨-, -, -, hver, -, -, -⟩ := rigExt_field_of_charP p k (p_eq_zero p k) G
  have key : ∀ m, (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) =
      rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m) := by
    intro m
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]
    rw [← SemiHom.ofHom_rig]
    exact T.base.red_smap trivial trivial (SemiHom.ofHom _) m
  have rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial x
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), T.base.red_eq_zero] at hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n', rfl⟩ := hbij.2 n
    have hm : m = p • n' := hbij.1 (by rw [hn, map_nsmul])
    exact (T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩
  have osurj := frobProj_omega_surjective G
  have h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega := by
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) ∈
          LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega := by
        rw [key, ← hver]; exact ⟨_, rfl⟩
      obtain ⟨w', hw'⟩ := hm
      obtain ⟨w, rfl⟩ := osurj w'
      exact ⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩
    · rintro ⟨w, rfl⟩
      have hw : (frobTwist (p_eq_zero p k) G).rigOfOmega ((frobProj (p_eq_zero p k) G).omega w) ∈
          LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G)) := by
        rw [hver]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hw
      obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial y
      exact ⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩
  have h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n := by
    intro m
    refine (T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
    · rw [hn]; exact (T.V_F G n).symm
    · rw [hn]; exact T.V_F G n
  refine ⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩
  rw [G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]
  constructor
  · intro hm
    obtain ⟨m', hm'⟩ := (h1 _).2 (by simpa using hm)
    have h0 : T.red G (m - T.V G m') = 0 := by rw [map_sub, hm', sub_self]
    obtain ⟨n, hn⟩ := (T.base.red_eq_zero G trivial _).1 h0
    refine ⟨m' + T.F G n, ?_⟩
    rw [map_add, T.V_F G n, ← hn, add_sub_cancel]
  · rintro ⟨n, rfl⟩
    obtain ⟨w, hw⟩ := (h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩
    exact ⟨w, hw⟩

end GlobalTheory.Dieu.Theory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitEqOfGermEq
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

namespace GlobalTheory.DualUnitGerm

theorem primeSpectrum_subsingleton (k : Type) [Field k] : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  have key : ∀ p : PrimeSpectrum (DualNumber k), p.asIdeal = maximalIdeal (DualNumber k) := by
    intro p
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro x hx
    have hn : IsNilpotent x := by
      rcases TrivSqZeroExt.isUnit_or_isNilpotent x with h | h
      · exact absurd h hx
      · exact h
    exact (nilpotent_iff_mem_prime.1 hn) p.asIdeal p.isPrime
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

theorem unit_eq_of_germ_eq : ∀ (k : Type) [Field k] (z : Sp (DualNumber k)) (u v : (DualNumber k)ˣ), gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn u) = gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn v) → u = v := by
  intro k _ z u v h
  have hs : Subsingleton (Sp (DualNumber k)) := primeSpectrum_subsingleton k
  have h1 : (unitOn u).val = (unitOn v).val := by
    refine TopCat.Presheaf.section_ext (Sp (DualNumber k)).sheaf ⊤ _ _ fun x hx => ?_
    obtain rfl : x = z := Subsingleton.elim _ _
    have := congrArg Units.val h
    rw [gm_val _ x ⊤ hx, gm_val _ x ⊤ hx] at this
    exact this
  exact Units.ext
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv).1 h1)

end GlobalTheory.DualUnitGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundaryStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  first | exact @GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | exact GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | (intros; apply GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' <;> assumption)
end

