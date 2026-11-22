import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupLocalCoordinatesAtOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

theorem coords_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ δ : Fin n → Derivation ℤ (G.left.presheaf.stalk (origin G)) (G.left.presheaf.stalk (origin G)), (∀ a O (hO : origin G ∈ O) f, δ a ((G.left.presheaf.germ O (origin G) hO).hom f) = (G.left.presheaf.germ O (origin G) hO).hom (dd a O f)) → ∃ z : Fin n → G.left.presheaf.stalk (origin G), (∀ i, evO G (z i) = 0) ∧ (∀ a i, evO G (δ a (z i)) = if a = i then 1 else 0) ∧ maximalIdeal (G.left.presheaf.stalk (origin G)) = (maximalIdeal R).map (constO G) ⊔ Ideal.span (Set.range z) := by
  intro R _ _ _ _ G _ _ hsm n v dd hinv δ hδ
  letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra
  obtain ⟨hN, hF, hFin⟩ := GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal R G hsm
  have key : ∀ a f, evO G (δ a f) = tanDer G (v a) f := by
    intro a f
    obtain ⟨O, hx, g, rfl⟩ := G.left.presheaf.exists_germ_eq f
    rw [hδ a O hx g]
    exact GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative R G (v a) (dd a) (hinv a) O hx g
  have hadd : ∀ a x y, tanDer G (v a) (x + y) = tanDer G (v a) x + tanDer G (v a) y := by
    intro a x y
    rw [← key, ← key, ← key, map_add, map_add]
  have hmul : ∀ a x y, tanDer G (v a) (x * y) = evO G x * tanDer G (v a) y + evO G y * tanDer G (v a) x := by
    intro a x y
    rw [← key, ← key, ← key, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  have hc : ∀ a r, tanDer G (v a) (algebraMap R _ r) = 0 := by
    intro a r
    rw [← key]
    show evO G (δ a (constO G r)) = 0
    rw [← GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial,
      GlobalTheory.Heat.isInv_constFn R G (v a) (dd a) (hinv a) ⊤ r, map_zero, map_zero]
  let φ : TanM (𝟙 (Sp R)) G →+ (G.left.presheaf.stalk (origin G) → R) :=
    { toFun := fun w => tanDer G w
      map_zero' := funext fun f => by
        have h := GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G 0 0 f
        rwa [zero_smul, zero_mul] at h
      map_add' := fun u w => funext fun f => GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector R G u w f }
  have hlin : ∀ (c : Fin n → R) f, tanDer G (∑ a, c a • v a) f = ∑ a, c a * tanDer G (v a) f := by
    intro c f
    have h1 : tanDer G (∑ a, c a • v a) f = φ (∑ a, c a • v a) f := rfl
    rw [h1, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G (c a) (v a) f
  have hbasis : ∀ D : G.left.presheaf.stalk (origin G) → R, (∀ x y, D (x + y) = D x + D y) →
      (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (algebraMap R _ r) = 0) →
      ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * tanDer G (v a) x := by
    intro D h1 h2 h3
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_tangentVector_of_originDerivation R G D h1 h2 h3
    refine ⟨fun a => v.repr w a, ?_, ?_⟩
    · intro x
      rw [← hw x, ← hlin]
      congr 1
      exact (v.sum_repr w).symm
    · intro c hc'
      have hw' : ∑ a, c a • v a = w := GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq R G _ _ fun f => by rw [hlin, hw, hc' f]
      funext a
      rw [← hw', v.repr_sum_self]
  obtain ⟨z, hz0, hz1, hz2⟩ := GlobalTheory.T.derivation_family_cotangent_basis R _ (evO G) (GlobalTheory.FormalOrigin.evO_constO R G) hF hFin n
    (fun a => tanDer G (v a)) hadd hmul hc hbasis
  exact ⟨z, hz0, fun a i => by rw [key]; exact hz1 a i, hz2⟩

end GlobalTheory.CoordsOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEighthPowerDiag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

theorem smul_eighth_power_diag : ∀ (X₀ X : Type) [AddCommGroup X₀] [AddCommGroup X] (K : (Fin 8 → X₀) ≃+ (Fin 8 → X)), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) → ∃ k : X₀ ≃+ X, ∀ mu, K mu = fun u => k (mu u) := by
  intro X₀ X _ _ K hK
  have hsel : ∀ (Y : Type) [AddCommGroup Y] (w : Fin 8) (nu : Fin 8 → Y),
      (fun u : Fin 8 => ∑ v, (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) u v • nu v)
        = fun _ => nu w := by
    intro Y _ w nu
    funext u
    simp [Matrix.of_apply]
  have hc : ∀ (mu : Fin 8 → X₀) (w : Fin 8), K (fun _ => mu w) = fun _ => K mu w := by
    intro mu w
    have h := hK (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) mu
    rw [hsel, hsel] at h
    exact h
  let f : X₀ →+ X :=
    { toFun := fun x => K (fun _ => x) 0
      map_zero' := by
        show K 0 0 = 0
        simp
      map_add' := by
        intro x y
        show K ((fun _ => x) + (fun _ => y)) 0 = _
        rw [map_add]
        rfl }
  have hform : ∀ (mu : Fin 8 → X₀) (u : Fin 8), K mu u = f (mu u) := by
    intro mu u
    show K mu u = K (fun _ => mu u) 0
    rw [hc]
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h1 : K (fun _ => x) = 0 := by
      funext u
      rw [hform]
      exact hx
    have h2 : (fun _ : Fin 8 => x) = 0 := K.injective (h1.trans (map_zero K).symm)
    exact congrFun h2 0
  have surj : Function.Surjective f := by
    intro y
    refine ⟨K.symm (fun _ => y) 0, ?_⟩
    have h := hform (K.symm fun _ => y) 0
    rw [← h]
    simp
  refine ⟨AddEquiv.ofBijective f ⟨inj, surj⟩, fun mu => funext fun u => ?_⟩
  exact hform mu u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadModelFibreAtPointIsGivenVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCore

theorem linComb_hom {S S' : Scheme.{0}} {A T : Over S} {A' T' : Over S'} [GrpObj A] [GrpObj A']
    (f : (T ⟶ A) →* (T' ⟶ A')) {r : ℕ} (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) :
    f (linComb y a) = linComb (fun i => f (y i)) a := by
  have h := map_list_prod f (List.ofFn fun i => y i ^ a i)
  rw [List.map_ofFn] at h
  exact h.trans (congrArg List.prod (congrArg List.ofFn (funext fun i => map_pow f (y i) (a i))))

theorem comp_linComb' {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (U : T' ⟶ T) {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) : U ≫ linComb y a = linComb (fun i => U ≫ y i) a :=
  linComb_hom (MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y) y a

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (M : ℕ) (h : ∀ i, y i ^ M = 1) : linComb y a ^ M = 1 := by
  unfold linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem push_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {T₀ : Over S} (U : T.left ⟶ T₀.left)
    (hU : U ≫ T₀.hom = T.hom ≫ f) {r : ℕ} (x : Fin r → (T ⟶ G')) (y : Fin r → (T₀ ⟶ G))
    (hxy : ∀ i, (x i).left ≫ φ = U ≫ (y i).left) (a : Fin r → ℕ) :
    (linComb x a).left ≫ φ = U ≫ (linComb y a).left := by
  let V : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk U hU
  have e : pushHom h T (linComb x a) = V ≫ linComb y a := by
    rw [linComb_hom, comp_linComb']
    exact congrArg (linComb · a) (funext fun i => Over.OverMorphism.ext (hxy i))
  exact congrArg (fun z => z.left) e

theorem unitOn_zpow {R : Type} [CommRing R] (c : Rˣ) (e : ℤ) : unitOn (c ^ e) = unitOn c ^ e := map_zpow _ c e

theorem final_pf : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A B : PolAV (Sp Ω)) (A₀ : PolAV (Sp F)) (σ : A.A ≅ B.A) (ψ : B.A.left ⟶ A₀.A.left), GlobalTheory.IsPolIso A B σ → IsGrpPullback B.A A₀.A (spMap em) ψ → LBIso B.L (A₀.L.pull ψ) → ∃ a : A.A.left ⟶ A₀.A.left, IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω _ _ em A B A₀ σ ψ hσ h hLB
  haveI := hσ.1
  obtain ⟨w, hw⟩ := hσ.2
  refine ⟨σ.hom.left ≫ ψ, ((isGrpPullback_of_iso σ).comp h).congr (Category.id_comp _) rfl, ?_⟩
  exact LBIso.trans A.isLB (pull_isLB B.isLB _) (pull_isLB A₀.isLB _) (LBIso.symm ⟨w, hw⟩)
    (GlobalTheory.ArcDataDescent.lbIso_pull hLB σ.hom.left rfl)

theorem fibre_descends : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (n J : ℕ), n.Prime → Odd n → 4 ≤ J → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ J → ∀ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (y₀ : Fin (2 * A.g) → (baseOver (Sp T) ⟶ P.A)) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) → (∀ i, (lev.pt i).left ≫ φ = spMap jT ≫ (y₀ i).left) → IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hP hL n J hn ho hJ hb ζ lev y₀ v' hζ hy hv
  obtain ⟨⟨hL1, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have := P.isAb.comm
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  have hgP : P.g = A.g := H1.dim_unique A.A.hom
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hP.1 P.smoothDim) A.smoothDim
    ((1 : baseOver (Sp Ω) ⟶ A.A).left (IsLocalRing.closedPoint Ω))
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    have : n ≠ 2 := by rintro rfl; exact absurd ho (by decide)
    omega
  have hm3 : 3 ≤ n ^ J := hn3.trans (Nat.le_self_pow (by omega) n)
  have hM0 : (n ^ J) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hF0 : (((n ^ J) ^ 2 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hΩ0 : (((n ^ J) ^ 2 : ℕ) : Ω) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hF0
  have hnΩ : (n : Ω) ≠ 0 := by
    rw [← map_natCast em]; exact (map_ne_zero em).2 (Nat.cast_ne_zero.2 hn.ne_zero)
  have hyt : ∀ i, y₀ i ^ ((n ^ J) ^ 2) = 1 := fun i =>
    GlobalTheory.T.pow_eq_one_of_isGrpPullback_of_injective_domain Ω T jT hinj A P φ hP (lev.pt i) (y₀ i) _ (hy i) (lev.torsion i)
  let ζT : Tˣ := Units.map (algebraMap F T).toMonoidHom ζ
  have hjζ : Units.map jT.toMonoidHom ζT = Units.map em.toMonoidHom ζ := by
    ext; simp [ζT, ← hcomp]
  have hpair : ∀ i j, WeilIs P.A P.L (((n ^ J) ^ 2 : ℕ) : ℤ) (y₀ i) (y₀ j) (unitOn ζT ^ stdSymp A.g i j) := fun i j => by
    have := GlobalTheory.T.commutatorPairing_spread_points_eq_spread_root Ω T jT hinj A P φ hP hL ((n ^ J) ^ 2) (lev.pt i) (lev.pt j) (y₀ i) (y₀ j) (ζT ^ stdSymp A.g i j)
      (Nat.one_le_iff_ne_zero.2 hM0) (hy i) (hy j) (hyt i) (hyt j)
      (by rw [map_zpow, hjζ, unitOn_zpow]; exact lev.pairing i j)
    rwa [unitOn_zpow] at this
  let tR : T →+* F := t.toRingHom
  have htζ : Units.map tR.toMonoidHom ζT = ζ := by ext; simp [ζT, tR]
  let A₀ := GlobalTheory.AmpleSymModel.polPull P (spMap tR)
  let ψ₀ : A₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap tR)
  have hA₀ : IsGrpPullback A₀.A P.A (spMap tR) ψ₀ := isGrpPullback_pullback P.A (spMap tR)
  have hLA₀ : LBIso A₀.L (P.L.pull ψ₀) := PolBaseChange.lbIso_refl (pull_isLB P.isLB _)
  obtain ⟨levF, hlevF⟩ := GlobalTheory.T.exists_level_structure_geometric_fibre_pullback T F tR P A₀ ψ₀ hA₀ hLA₀ A.g ((n ^ J) ^ 2) hgP ζT ζ hF0 htζ hζ y₀ hyt hpair
  have cover : ∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ (n ^ J) = 1 →
      ∃ a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2),
      ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
        linComb y₀ (fun i => (a i).val)) ^ (n ^ J) = z := by
    intro z hz
    obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hA₀ (𝟙 (Sp F)) (spMap tR) (Category.id_comp _).symm
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_levelPoint_pow_eq' F A₀ (n ^ J) A.g hgP _ levF (e.symm z) (by omega) (by rw [← map_pow, hz, map_one])
    refine ⟨a, ?_⟩
    have key : e (GlobalTheory.levelPoint levF hgP a) =
        (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
          linComb y₀ (fun i => (a i).val) := by
      apply Over.OverMorphism.ext
      refine (he _).trans ((congrArg (fun z => z.left ≫ ψ₀) (GlobalTheory.ThetaPtDet.levelPoint_eq levF hgP a)).trans ?_)
      exact push_linComb hA₀ (T := baseOver (Sp F)) (T₀ := baseOver (Sp T)) (spMap tR) (by simp) _ _ hlevF _
    rw [← key, ← map_pow, ha, MulEquiv.apply_symm_apply]
  have hxF : ∀ a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2), (GlobalTheory.levelPoint lev rfl a).left ≫ φ =
      spMap jT ≫ (linComb y₀ (fun i => (a i).val)).left := fun a =>
    (congrArg (fun z => z.left ≫ φ) (GlobalTheory.ThetaPtDet.levelPoint_eq lev rfl a)).trans
      (push_linComb hP (T := baseOver (Sp Ω)) (T₀ := baseOver (Sp T)) (spMap jT) (by simp) _ _ hy _)
  have thF : IsThetaPt P (n ^ J)
      (fun a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2) =>
        (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
          linComb y₀ (fun i => (a i).val))
      (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v' a)) :=
    GlobalTheory.T.isThetaPt_fibre_spread_model_at_fieldPoint F Ω T em jT t hft hinj hcomp A P φ hP hL (n ^ J) (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2))
      (GlobalTheory.levelPoint lev rfl) (fun a => linComb y₀ (fun i => (a i).val)) v' ho.pow hm3 hxF
      (fun a => linComb_pow_eq_one _ _ _ hyt) cover hv
  let B := GlobalTheory.AmpleSymModel.polPull A₀ (spMap em)
  let ψ₁ : B.A.left ⟶ A₀.A.left := pullback.fst A₀.A.hom (spMap em)
  have hB₁ : IsGrpPullback B.A A₀.A (spMap em) ψ₁ := isGrpPullback_pullback A₀.A (spMap em)
  have hLB₁ : LBIso B.L (A₀.L.pull ψ₁) := PolBaseChange.lbIso_refl (pull_isLB A₀.isLB _)
  have hsp : spMap em ≫ spMap tR = spMap (em.comp tR) := by simp [spMap, ← Spec.map_comp]
  have hB : IsGrpPullback B.A P.A (spMap em ≫ spMap tR) (ψ₁ ≫ ψ₀) := hB₁.comp hA₀
  have hLB : LBIso B.L (P.L.pull (ψ₁ ≫ ψ₀)) := GlobalTheory.ArcDataDescent.lbIso_pull_pull P.isLB ψ₀ ψ₁ rfl
  have hBζ : Units.map (em.comp tR).toMonoidHom ζT = Units.map em.toMonoidHom ζ := by ext; simp [ζT, tR]
  obtain ⟨levB, hlevB⟩ := GlobalTheory.T.exists_level_structure_geometric_fibre_pullback T Ω (em.comp tR) P B (ψ₁ ≫ ψ₀) (hB.congr hsp rfl) hLB A.g ((n ^ J) ^ 2) hgP ζT _
    hΩ0 hBζ (hζ.map_of_injective (Units.map_injective (f := em.toMonoidHom) em.injective)) y₀ hyt hpair
  have thΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P em (x := spMap em ≫ spMap tR) rfl thF
  have key : ∀ (s : Sp Ω ⟶ Sp T) (_ : s = (baseOver (Sp Ω)).hom ≫ (spMap em ≫ spMap tR))
      (x₀ : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → (Over.mk s ⟶ P.A))
      (v : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → Γ(Sp Ω, ⊤)),
      (∀ a, (x₀ a).left = (GlobalTheory.levelPoint levB hgP a).left ≫ (ψ₁ ≫ ψ₀)) → IsThetaPt P (n ^ J) x₀ v →
      IsThetaPt B (n ^ J) (GlobalTheory.levelPoint levB hgP) v := by
    rintro s rfl x₀ v hx h
    have := B.isAb.comm
    exact (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) hB hLB hx
      (fun a => (congrArg (· ^ ((n ^ J) ^ 2)) (GlobalTheory.ThetaPtDet.levelPoint_eq levB hgP a)).trans
        (linComb_pow_eq_one _ _ _ fun i => levB.torsion _)) v).2 h
  have thB := key _ (Category.id_comp _).symm _ _ (fun a => by
    refine Eq.symm ((congrArg (fun z => z.left ≫ (ψ₁ ≫ ψ₀)) (GlobalTheory.ThetaPtDet.levelPoint_eq levB hgP a)).trans ?_)
    refine (push_linComb hB (T := baseOver (Sp Ω)) (T₀ := baseOver (Sp T)) (spMap em ≫ spMap tR) (by simp) _ _
      (fun i => (hlevB i).trans (by rw [hsp])) _).trans ?_
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]) thΩ
  have hN' : n ^ J = n ^ (J - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.thetaPt_determines hL1 A.g n 2 (J - 4) ((n ^ 2) ^ 2) (n ^ J) hn ho le_rfl rfl hN' hb Ω hnΩ
    A B rfl hgP _ lev levB _ hv thB
  exact ⟨A₀, final_pf F Ω em A B A₀ σ ψ₁ hσ hB₁ hLB₁⟩

end GlobalTheory.MumCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mem_map_algebraMap_of_algHom {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) :
    e x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (e : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem K_inf_eq_and_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ →
    ∀ S S' : Sys I π s₀, S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ∧
      (S.Full hI → S'.Full hI) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc
  have key : ∀ S S' : Sys I π s₀,
      S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ≤ S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    intro S S' c hc'
    obtain ⟨hcK, hcI⟩ := hc'
    obtain ⟨Φ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S S'
    obtain ⟨-, h2, h3⟩ := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀ S S' Φ
    obtain ⟨z, z', hz, hmk, hmk', hzz⟩ := h3 c hcI
    have h0 : H1.mk _ z = 0 := hmk.trans (LinearMap.mem_ker.1 hcK)
    obtain ⟨g, hg, hdg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hc S z hz h0
    refine ⟨LinearMap.mem_ker.2 ?_, hcI⟩
    rw [← hmk']
    refine H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
    funext U V a
    rw [h2 g hg U V a, hdg, hzz]
  refine fun S S' ↦ ⟨le_antisymm (key S S') (key S' S), fun hF z₁' hz₁' ↦ ?_⟩
  obtain ⟨Ψ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S' S
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀ S' S Ψ
  obtain ⟨z₁, hz₁, hz₁e⟩ := h1 z₁' hz₁'
  obtain ⟨c, hcI, hc₁⟩ := hF z₁ hz₁
  obtain ⟨y', y, hy'I, hy', hy, hyy⟩ := h3 c hcI
  have hyI : S.IsIdealValuedLiftSystemCocycle y := fun U V a ↦ by
    rw [hyy]; exact mem_map_algebraMap_of_algHom (Ψ.φ V : S'.F.obj V →ₐ[R] S.F.obj V) (hy'I U V a)
  have hd : H1.mk _ (y - z₁) = 0 := by rw [map_sub, hy, hc₁, sub_self]
  obtain ⟨g, hg, hdg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hc S (y - z₁)
    (fun U V a ↦ Ideal.sub_mem _ (hyI U V a) (hz₁ U V a)) hd
  let g' : C0 S'.F := fun W ↦ (Ψ.φ W).symm (g W)
  have hg' : S'.IsIdealValuedLiftSystemCochain g' := fun W ↦
    mem_map_algebraMap_of_algHom ((Ψ.φ W).symm : S.F.obj W →ₐ[R] S'.F.obj W) (hg W)
  have hgg : (fun W ↦ Ψ.φ W (g' W)) = g := funext fun W ↦ AlgEquiv.apply_symm_apply _ _
  refine ⟨c, hcI, hy'.symm.trans (H1.mk_eq_mk.2 ⟨g', ?_⟩)⟩
  funext U V a
  apply (Ψ.φ V).injective
  have e := h2 g' hg' U V a
  rw [hgg, hdg] at e
  rw [← e]
  show y.1 U V a - z₁.1 U V a = Ψ.φ V (y'.1 U V a - z₁'.1 U V a)
  rw [map_sub, hyy, hz₁e]
end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_app_eq_sum_mul_of_comm : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  intro X Y S S' T X' g h gp gp' hgp fst snd hsq α t hpb l h1 h2 W U hWU n c b b' hb
  subst h1
  have le : fst ⁻¹ᵁ W ≤ snd ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hsq, Scheme.Hom.comp_preimage]
    exact fun x hx => hWU hx
  refine ⟨∑ m, (fst.app W).hom (c m) * (snd.appLE (h ⁻¹ᵁ U) (fst ⁻¹ᵁ W) le).hom (b' m), ?_⟩
  have hid : ∀ z : Γ(Y, (l ≫ fst) ⁻¹ᵁ W), (Y.presheaf.map (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op).hom z = z := by
    intro z
    have : (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op = 𝟙 (Opposite.op ((l ≫ fst) ⁻¹ᵁ W)) := rfl
    erw [this, Y.presheaf.map_id]
    rfl
  rw [hid, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  rw [← hb m]
  have key : ∀ (f₁ f₂ : Y ⟶ S') (e : f₁ = f₂) (V : Y.Opens) (e₁ e₂), f₁.appLE (h ⁻¹ᵁ U) V e₁ = f₂.appLE (h ⁻¹ᵁ U) V e₂ := by
    intro f₁ f₂ e V e₁ e₂; subst e; rfl
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (b' m)) (key _ _ h2 _ _ _)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimage
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.QCoh

open TensorProduct in

theorem nontrivial_fibre_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

theorem mem_support_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_of_isBaseChange hl _ _ rfl

theorem support_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  ext y
  obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
  have hfy : f y ∈ V := e hy
  rw [Set.mem_preimage, mem_support_iff_primeIdealOf hU ⟨y, hy⟩,
    mem_support_iff_primeIdealOf hV ⟨f y, hfy⟩]
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have := finite_sections G hV
  rw [mem_support_of_isBaseChange (isBaseChange_pullbackSections f G hU hV e)]
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hy
  convert Iff.rfl using 2
  exact h.symm

end GlobalTheory.QCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.NearSurj

theorem surjective_of_open_closedFibre : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  intro R _ _ U hs hsu V hV
  have : Smooth (U ⊗ U).hom := inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))
  obtain ⟨u, hu⟩ := U.hom.surjective (closedPoint R)
  let d : U.left ⟶ (U ⊗ U).left := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hd : (U ⊗ U).hom (d u) = closedPoint R := by
    rw [← hu, ← Scheme.Hom.comp_apply]
    change (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _
    rw [pullback.lift_fst_assoc, Category.id_comp]
  have hmem : d u ∈ V := hV _ hd
  have ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom) := (V.ι ≫ (U ⊗ U).hom).isOpenMap
  refine ⟨fun r => ?_⟩
  obtain ⟨y, hy⟩ : d u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  have h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R := by
    rw [Scheme.Hom.comp_apply, hy]; exact hd
  exact (IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩

end GlobalTheory.Mum.NearSurj
end

