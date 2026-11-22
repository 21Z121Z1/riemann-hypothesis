import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.MumLin

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem exists_gen_diff (hL : L.IsLB) (σ : X ⟶ X) (h : LBIso L (L.pull σ)) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, σ] ![1, -1]), w.IsGen := by
  have h1 := (GlobalTheory.TripleCompare.lbIso_iff_pull_id L (L.pull σ)).1 h
  obtain ⟨t, ht⟩ := (GlobalTheory.TripleCompare.lbIso_iff_gen _ _ _ _).1 h1
  obtain ⟨w, hw, -⟩ := DVR.gen_transport (φ' := ![𝟙 X, σ]) (ε' := ![1, -1]) hL (by
    rw [DVR.sameSum_iff_fsum, DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two]) t ht
  exact ⟨w, hw⟩

theorem corr_of_pull_section (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    (hs : DVR.fsum φ ε = DVR.fsum φ' ε') (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (hp : Function.Surjective p.appTop.hom)
    (H : LB.Gen.Corr L _ ε _ ε' (LB.pullGen L φ ε t z) (LB.pullGen L φ' ε' t' z)) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hq : (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')).IsGen :=
    DVR.mulGen_isGen_of_isGen t ht _ (DVR.invGen_isGen_of_isGen t' ht')
  have h0 : DVR.fsum (fun k => 𝟙 Y ≫ Sum.elim φ φ' k) (Sum.elim ε fun k => -ε' k) = 0 := by
    rw [DVR.fsum_comp, DVR.fsum_sumElim, DVR.fsum_neg, hs, add_neg_cancel, Finsupp.mapDomain_zero]
  obtain ⟨c, hc⟩ := DVR.exists_value hL _ _ _ hq (𝟙 Y) h0
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Y) (w : W) (J : (W ⟶ X) → L.ι), Good L w J →
      val (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) r w J = gm r w ⊤ c := by
    intro W r w J hJ
    have e1 := val_pull hJ (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) (𝟙 Y) r
    rw [Category.comp_id] at e1
    rw [← e1, val_of _ r w J (fun k => J (r ≫ 𝟙 Y ≫ Sum.elim φ φ' k)) (fun _ => rfl),
      ← hc _ (fun k₁ k₂ e => by simp only [e])]
    exact gm_res r w le_top (hJ.mem _ r) c
  have hz1 : ∀ w : Z, gm z w ⊤ c = 1 := by
    intro w
    obtain ⟨J, hJ, -⟩ := exists_good (Z := Z) L hL w (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e1 := val_pull hJ t z (𝟙 Z)
    have e2 := val_pull hJ t' z (𝟙 Z)
    rw [Category.id_comp] at e1 e2
    rw [← key Z z w J hJ, val_mul hJ, val_inv, ← e1, ← e2, val_corr hJ H, mul_inv_cancel]
  obtain ⟨d, hd⟩ := hp c.val
  have d1 : d = 1 := fn_ext fun w _ => by
    have e' : gm (𝟙 Z ≫ z) w ⊤ c = 1 := by rw [Category.id_comp]; exact hz1 w
    have e'' := (gs_pull (𝟙 Z ≫ z) p w ⊤ trivial d).symm.trans ((congrArg (gs (𝟙 Z ≫ z) w ⊤) hd).trans
      ((gs_unit _ w ⊤ trivial c).trans (congrArg Units.val e')))
    rw [Category.assoc, hzp, Category.comp_id] at e''
    rw [e'', gs_eq _ w ⊤ trivial, map_one, map_one, Units.val_one]
  have c1 : c = 1 := Units.ext (by rw [← hd, d1, map_one]; rfl)
  refine corr_of_val hL fun y J hJ => ?_
  have e := key Y (𝟙 Y) y J hJ
  rw [c1, map_one, val_mul hJ, val_inv, mul_inv_eq_one] at e
  exact e

theorem exists_linearisation : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  intro T X π e he hπ L hL ⟨r, hr⟩ Ga _ ρ θ hρ hθ heρ hiso
  have hex : ∀ a, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e)
        (LB.mulGen L _ _ _ _ r (LB.invGen L _ _ (LB.pullGen L _ _ r (θ a)))) := by
    intro a
    obtain ⟨w, hw⟩ := exists_gen_diff hL (ρ a) (hiso a)
    refine DVR.exists_normalized_to hL _ _ w hw π e he _ _ _
      (DVR.mulGen_isGen_of_isGen r hr _ (DVR.invGen_isGen_of_isGen _ (DVR.pullGen_isGen_of_isGen _ _ r hr _))) ?_
    rw [DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two, heρ a]
  choose u hu hue using hex
  refine ⟨u, hu, fun a c => ?_⟩
  refine corr_of_pull_section hL (hu _) (DVR.mulGen_isGen_of_isGen _ (hu a) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hu c) _))
    ?_ π e he hπ ?_
  · rw [DVR.fsum_sumElim]
    simp only [DVR.fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Category.comp_id, hρ]
    rw [add_assoc, ← add_assoc (Finsupp.single (ρ a) (-1 : ℤ)), ← Finsupp.single_add, neg_add_cancel, Finsupp.single_zero,
      zero_add]
  · refine corr_of_val hL fun y J hJ => ?_
    have v1 := val_corr hJ (hue (a * c)) (𝟙 T)
    have v2 := val_corr hJ (hue a) (𝟙 T)
    have v3 := val_corr hJ (hue c) (θ a)
    simp only [val_mul hJ, val_inv, val_pull hJ, Category.id_comp, Category.assoc, hθ] at v1 v2 v3 ⊢
    rw [heρ a, v1, v2, v3, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.MumLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open scoped Pointwise

namespace GlobalTheory.LocalNormalExt

theorem exists_eq_of_mul_mem_integralClosure
    (R K K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra R K'] [IsScalarTower R K K']
    (P : Ideal (integralClosure R K')) [P.IsMaximal]
    (x : K) (s : integralClosure R K') (hs : s ∉ P)
    (hx : algebraMap K K' x * (s : K') ∈ integralClosure R K') :
    ∃ r : R, algebraMap R K r = x := by
  classical
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R K' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply K K' L]; rfl)
  haveI : FiniteDimensional K L := inferInstance
  haveI : IsGalois K L := inferInstance
  haveI : IsScalarTower R R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure R L
  let C := integralClosure R K'
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let f : C →ₐ[R] S := ((IsScalarTower.toAlgHom R K' L).comp C.val).codRestrict S
    (fun c => (c.2 : IsIntegral R (c : K')).map (IsScalarTower.toAlgHom R K' L))
  have hfv : ∀ c : C, ((f c : S) : L) = algebraMap K' L (c : K') := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro c d h
    have := congrArg (fun u : S => (u : L)) h
    simp only [hfv] at this
    exact Subtype.ext ((algebraMap K' L).injective this)
  letI : Algebra C S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.IsIntegral C S := ⟨fun u => (Algebra.IsIntegral.isIntegral (R := R) u).tower_top⟩
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C S)).mp hfinj]; exact bot_le)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let J : Ideal S :=
    { carrier := {u | ∃ v : S, u * algebraMap R S a = algebraMap R S b * v}
      add_mem' := by
        rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
        exact ⟨v₁ + v₂, by rw [add_mul, h₁, h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨v, h⟩
        exact ⟨c * v, by rw [smul_eq_mul, _root_.mul_assoc, h, mul_left_comm]⟩ }
  have hJg : ∀ (g : S ≃ₐ[R] S) (u : S), u ∈ J → g u ∈ J := by
    rintro g u ⟨v, h⟩
    exact ⟨g v, by rw [← g.commutes a, ← g.commutes b, ← map_mul, h, map_mul]⟩

  have e1 : ∀ r : R, ((algebraMap R S r : S) : L) = algebraMap K L (algebraMap R K r) :=
    fun _ => rfl
  have hbL : algebraMap K L (algebraMap R K b) ≠ 0 := (map_ne_zero _).mpr hb0
  have htJ : f s ∈ J := by
    refine ⟨f ⟨_, hx⟩, ?_⟩
    apply Subtype.ext
    show (f s : L) * ((algebraMap R S a : S) : L) = ((algebraMap R S b : S) : L) * (f ⟨_, hx⟩ : L)
    rw [hfv, hfv, e1, e1]
    simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply K K' L, ← hab, map_div₀]
    field_simp
  have hmax : ∀ (I : Ideal S) [I.IsMaximal], I.under R = IsLocalRing.maximalIdeal R :=
    fun I _ => IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨N, hNmax, hJN⟩ := Ideal.exists_le_maximal J hne
    haveI : Finite (S ≃ₐ[R] S) := Finite.of_equiv _ (galRestrict R K L S).toEquiv
    haveI : Algebra.IsInvariant R S (S ≃ₐ[R] S) := Algebra.isInvariant_of_isGalois' R K L S
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := R) (B := S) (G := S ≃ₐ[R] S) Q N
      ((hmax Q).trans (hmax N).symm)
    have h1 : g • f s ∈ g • Q := by
      rw [← hg]; exact hJN (hJg g _ htJ)
    have h2 : f s ∈ Q := (Ideal.smul_mem_pointwise_smul_iff).mp h1
    exact hs (by rw [← hQ]; exact h2)
  obtain ⟨v, hv⟩ : (1 : S) ∈ J := hJtop ▸ Submodule.mem_top
  have hvL : (v : L) = algebraMap K L x := by
    have := congrArg (fun u : S => (u : L)) hv
    simp only [_root_.one_mul, Subalgebra.coe_mul, e1] at this
    rw [← hab, map_div₀, this]
    field_simp
  have hint : IsIntegral R (algebraMap K L x) := hvL ▸ v.2
  have hxint : IsIntegral R x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hxint

theorem exists_local_normal_domain_of_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  intro R _ _ _ _ _ _ K' _ _ _
  classical
  let K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C := integralClosure R K'
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing R K K' C
  haveI : IsDomain C := inferInstance
  obtain ⟨m', hm'⟩ := Ideal.exists_maximal C
  obtain ⟨R', _, _, _⟩ : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra C R'),
      IsLocalization.AtPrime R' m' :=
    ⟨Localization.AtPrime m', inferInstance, inferInstance, inferInstance⟩
  haveI : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' m'
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := m'.primeCompl) (S := R') m'.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing m'.primeCompl R' inferInstance
  haveI : IsIntegrallyClosed R' :=
    isIntegrallyClosed_of_isLocalization R' m'.primeCompl m'.primeCompl_le_nonZeroDivisors
  letI : Algebra R' K' := (IsLocalization.lift (M := m'.primeCompl) (S := R') (g := algebraMap C K')
    (fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C K')).mpr
      (fun h => y.2 (h ▸ m'.zero_mem))))).toAlgebra
  haveI : IsScalarTower C R' K' :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsLocalization.lift_eq _ c).symm)
  haveI : IsFractionRing R' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m'.primeCompl R' K'
  let e : FractionRing R' ≃+* K' :=
    (FractionRing.algEquiv R' K').toRingEquiv
  have he : ∀ w : R', e (algebraMap R' _ w) = algebraMap R' K' w := fun w =>
    (FractionRing.algEquiv R' K').commutes w
  have hRC : ∀ r : R, algebraMap C K' (algebraMap R C r) = algebraMap K K' (algebraMap R K r) :=
    fun _ => rfl
  have hinjRC : Function.Injective (algebraMap R C) := by
    intro a b h
    have := congrArg (algebraMap C K') h
    rw [hRC, hRC] at this
    exact IsFractionRing.injective R K ((algebraMap K K').injective this)
  have hinjCR' : Function.Injective (algebraMap C R') :=
    IsLocalization.injective R' m'.primeCompl_le_nonZeroDivisors
  have hcomap : m'.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m')
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap C R').comp (algebraMap R C), e, ?_, hinjCR'.comp hinjRC, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have h1 : algebraMap R C r ∈ m' := by
      rw [← Ideal.mem_comap, hcomap]; exact hnu
    have h2 : algebraMap C R' (algebraMap R C r) ∈ IsLocalRing.maximalIdeal R' := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R' m']; exact h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hr
  · intro r
    rw [he]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C R' K', hRC]
  · intro x w hw
    rw [he] at hw
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective m'.primeCompl w
    have hmul : algebraMap K K' x * (s : C) = (c : K') := by
      rw [← hw]
      have := congrArg (algebraMap R' K') (IsLocalization.mk'_spec R' c s)
      rw [map_mul, ← IsScalarTower.algebraMap_apply C R' K', ← IsScalarTower.algebraMap_apply C R' K'] at this
      exact this
    exact exists_eq_of_mul_mem_integralClosure R K K' m' x (s : C) s.2 (hmul ▸ c.2)

end GlobalTheory.LocalNormalExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatEnd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem exists_matEnd {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! z : T' ⟶ B, ∀ a, z ≫ pr a = y a) (a b : Fin 8) :
    ∃ f : B ⟶ B, MatEnd pr a b f := by
  obtain ⟨f, hf, -⟩ := hu B (fun w => if w = a then pr b else 1)
  have ext : ∀ {T : Over S} (z z' : T ⟶ B), (∀ w, z ≫ pr w = z' ≫ pr w) → z = z' := by
    intro T z z' h
    obtain ⟨_, -, hz⟩ := hu T (fun w => z' ≫ pr w)
    exact (hz z h).trans (hz z' fun _ => rfl).symm
  have mul : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    intro T x y
    refine ext _ _ fun w => ?_
    have hw := hpr w
    have e : ((x ≫ f) * (y ≫ f)) ≫ pr w = (x ≫ f ≫ pr w) * (y ≫ f ≫ pr w) := by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc]
    rw [e, Category.assoc, hf]
    split_ifs
    · have := hpr b
      rw [MonObj.mul_comp]
    · simp
  refine ⟨f, ⟨?_, ?_⟩, hf⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ B) ≫ f = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (B ⊗ B) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem matOn_exists : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (C : Over (Sp S.R)) [GrpObj C] [IsCommMonObj C] (pr : Fin 8 → (ρ.P.A ⟶ C)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp S.R)) (y : Fin 8 → (T' ⟶ C)), ∃! z : T' ⟶ ρ.P.A, ∀ a, z ≫ pr a = y a) → ∀ a b, ∃ f, MatOn FinalForm pr a b f := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm hU C _ _ pr hpr hu a b
  obtain ⟨f₁, hf₁⟩ := exists_matEnd pr hpr hu a b
  have : IsMonHom f₁ := hf₁.1

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ f₁
  have hw'l : w'.left ≫ ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ f₁.left := by
    have := congrArg (fun z => z.left) (pa (𝟙 _))
    simpa [pushPt] using this
  obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
  refine ⟨F, hF, f₁, hf₁, ?_⟩
  have hsep : IsSeparated FinalForm.G.hom := FinalForm.semi.separated
  have hsm : Smooth FinalForm.G.hom := FinalForm.semi.smooth
  have hQf : Flat Q.hom := MorphismProperty.of_isPullback (P := @Flat) FinalForm.cart.1 inferInstance
  have hqc : QuasiCompact M.pt := by
    have : IsSeparated M.s := M.sep
    have : QuasiCompact (M.pt ≫ M.s) := by rw [M.pt_s]; infer_instance
    exact QuasiCompact.of_comp M.pt M.s
  have hdom : IsSchemeTheoreticallyDominant M.pt := .of_isDominant M.pt
  let p : pullback ρ.P.A.hom FinalForm.u₀ ⟶ M.Z := Q.hom ≫ U₀.ι
  let j := pullback.fst p M.pt
  have hj : j ≫ Q.hom = pullback.snd p M.pt ≫ x := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, hx]
    exact pullback.condition
  let k : pullback p M.pt ⟶ pullback FinalForm.G.hom M.pt := pullback.lift (j ≫ FinalForm.φ) (pullback.snd p M.pt) (by
    rw [Category.assoc, FinalForm.cart.1.w]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst FinalForm.G.hom M.pt = j ≫ FinalForm.φ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd p M.pt := pullback.lift_snd _ _ _
  have hkν : k ≫ ν = j := by
    apply FinalForm.cart.1.hom_ext
    · rw [Category.assoc, hν₁, hk₁]
    · rw [Category.assoc, hν₂, ← Category.assoc, hk₂, hj]
  have hF' : ((Over.pullback M.pt).map F).left ≫ pullback.fst FinalForm.G.hom M.pt = pullback.fst FinalForm.G.hom M.pt ≫ F.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hw₂ : w'.left ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd FinalForm.G.hom M.pt := Over.w w'
  have key : k ≫ w'.left ≫ ν = j ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hw'l]
      simp only [← Category.assoc]
      rw [hkν]
      simp only [Category.assoc, Over.pullback_map_left]
      exact congrArg (j ≫ ·) (pullback.lift_fst _ _ _).symm
    · have e : ((Over.pullback FinalForm.u₀).map f₁).left ≫ Q.hom = Q.hom := Over.w ((Over.pullback FinalForm.u₀).map f₁)
      show (k ≫ w'.left ≫ ν) ≫ Q.hom = (j ≫ ((Over.pullback FinalForm.u₀).map f₁).left) ≫ Q.hom
      simp only [Category.assoc]
      rw [hν₂, e, hj, ← Category.assoc w'.left, hw₂, ← Category.assoc, hk₂]
  refine GlobalTheory.SS.GenProj.ext_of_dense j FinalForm.G.hom ?_ ?_
  · have e1 : j ≫ FinalForm.φ ≫ F.left = k ≫ w'.left ≫ ν ≫ FinalForm.φ := by
      rw [hν₁, ← hFw, hF', ← Category.assoc k, hk₁, Category.assoc]
    rw [e1]
    simp only [← Category.assoc] at key ⊢
    rw [key]
  · rw [Category.assoc, Category.assoc, Over.w F, FinalForm.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraph
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_modif_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  intro R _ _ o _ b Z s hs y hy
  let ℓ : Sp (FractionRing R) ⟶ pullback s (spMap b) := pullback.lift y (jK R) hy
  have : QuasiCompact ℓ := inferInstance
  have : IsProper (pullback.snd s (spMap b)) := inferInstance
  refine ⟨{ S := ℓ.image
            π := ℓ.imageι ≫ pullback.snd s (spMap b)
            proper := inferInstance
            integral := isIntegral_image_of_field ℓ
            gp := ℓ.toImage
            gp_π := by rw [ℓ.toImage_imageι_assoc, pullback.lift_snd]
            dominant := inferInstance }, ℓ.imageι ≫ pullback.fst s (spMap b), ?_, ?_⟩
  · show ℓ.toImage ≫ ℓ.imageι ≫ pullback.fst s (spMap b) = y
    rw [ℓ.toImage_imageι_assoc, pullback.lift_fst]
  · show (ℓ.imageι ≫ pullback.fst s (spMap b)) ≫ s = (ℓ.imageι ≫ pullback.snd s (spMap b)) ≫ spMap b
    rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalLiftOfDefectCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_naturalLift_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  first | exact @GlobalTheory.LiftSys.exists_natLift_of_defect | exact GlobalTheory.LiftSys.exists_natLift_of_defect | (intros; apply GlobalTheory.LiftSys.exists_natLift_of_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsCharacterUnitKernelActionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_characterUnit_kernel_action : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∀ y : (A' ⊗ T).left, ∃ V : (A' ⊗ T).left.Opens, y ∈ V ∧ ∃ e : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ V)ˣ, ∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)) (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)), res h₁ (pullU (actMap i T).left _ e) = res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ e) := by
  first | exact @GlobalTheory.CharKer.exists_nhds_charUnit | exact GlobalTheory.CharKer.exists_nhds_charUnit | (intros; apply GlobalTheory.CharKer.exists_nhds_charUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonvanishing_extension_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → τ (H.rt : E) = H.rt0 → SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → SecU Xo c U τ σ → Restricts Z U τ σZ σ → ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ := by
  first | exact @GlobalTheory.DetLine.ExtendNormal.exists_extension | exact GlobalTheory.DetLine.ExtendNormal.exists_extension | (intros; apply GlobalTheory.DetLine.ExtendNormal.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroScalarWeightCuspFormComponentStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  first | exact @GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero | exact GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero | (intros; apply GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfFiniteFreeBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_of_finite_free_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  first | exact @GlobalTheory.FlatGenDescent.exists_sec_of_free | exact GlobalTheory.FlatGenDescent.exists_sec_of_free | (intros; apply GlobalTheory.FlatGenDescent.exists_sec_of_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_kodairaSpencerCoordinate_affine_off_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), GlobalTheory.Published.AbelianDeRham → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens), IsAffineOpen W → W ≤ ksOpen M i k → ∃ a : Γ(M.X, W), ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W), KSRel M i k z (GlobalTheory.FlagMod.ev z W hz a) := by
  first | exact @GlobalTheory.CompHS.exists_regular_ksRel | exact GlobalTheory.CompHS.exists_regular_ksRel | (intros; apply GlobalTheory.CompHS.exists_regular_ksRel <;> assumption)
end

