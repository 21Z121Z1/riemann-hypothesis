import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointPlaceCondition
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.HtGen.RegOver

theorem mem_range_j {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {x : V.X}
    (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_horizPt_over {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : V.X.Opens) (z : V.X)
    (g : Γ(V.X, W)) (hz : z ∈ W) (hg : g ≠ 0) (hzg : z ∉ V.X.basicOpen g) (a : 𝓞 F) (ha : a ∈ (V.p z).asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      a ∈ v.asIdeal ∧ y ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = y ≫ V.j ∧
      ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ V.X.basicOpen g ∧ below (y ≫ V.j) ∈ V.X.basicOpen g := by
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(V.X, U) := V.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral V.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(V.X, U), hU.fromSpec x ∈ V.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ V.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  refine ⟨v, e, V.pb.lift _ _ hw, yt, ?_, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_⟩
  · have e₁ : V.p z = Spec.map (GlobalTheory.TrueGeo.HorizPt.strHom V.p U) (hU.primeIdealOf ⟨z, hzU⟩) := by
      rw [← fromSpec_str V.p hU]
      exact congrArg V.p (hU.fromSpec_primeIdealOf ⟨z, hzU⟩).symm
    rw [e₁] at ha
    have h₄ : algebraMap (𝓞 F) Γ(V.X, U) a ∈ 𝔪 := hle' ha
    rw [← h₂] at h₄
    by_contra hv
    refine (IsLocalRing.mem_maximalIdeal _).1 h₄ (GlobalTheory.TrueGeo.RegCrit.isUnit_of_one_le e _ ?_)
    rw [h₁ a, e.w_alg, ← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_eq_one_iff_notMem F v a).2 hv).ge
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

open GlobalTheory.TrueGeo.RegCrit in

theorem regAt_of_integral_values_over : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (U : V.X.Opens) (g : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) g) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) → ∀ x ∈ U, (l : 𝓞 F) ∈ (V.p x).asIdeal → RegAt x g := by
  intro F _ _ Y V l U f hgen hf x hx hl
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  have hlz : (l : 𝓞 F) ∈ (V.p z).asIdeal := by
    have hne : (V.p z).asIdeal ≠ ⊥ := fun h => by
      obtain ⟨z', rfl⟩ := mem_range_j V h
      exact (zeroAt_iff.1 hzero).2 ((unitAt_iff (inv_ne_zero hf0)).2 ⟨hzero.regAt, (inv_inv f).symm ▸ hgen z' hzU⟩)
    have hle : (V.p z).asIdeal ≤ (V.p x).asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous))
    have hmax : (V.p z).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal (R := 𝓞 F) (V.p z).isPrime hne
    rwa [hmax.eq_of_le (V.p x).isPrime.ne_top hle]
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ V.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hv, hy, hc, hW, hn, hu⟩ := exists_horizPt_over V _ z g hzW' hg0 hzg _ hlz
  have hle := hf v e y yt hv hy hc fun p hp => (hW hp).2
  have hu' : below (y ≫ V.j) ∈ V.X.basicOpen g := hu
  have hb : below (y ≫ V.j) ∈ W₀ ⊓ U := V.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y ≫ V.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y ≫ V.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ V.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt
  have hone : TrueGeo.valAt (y ≫ V.j) (1 : V.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ V.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

end GlobalTheory.HtGen.RegOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplit
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj GlobalTheory.HTMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

theorem dlog_regular_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ), SplitK t ξ (p ^ n) → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A K] [IsFractionRing A K] (x₀ : Sp A ⟶ X), spMap (algebraMap A K) ≫ x₀ = ξ → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), (∀ i, IsTanAtG t x₀ (e i)) → ∀ χ : TorsK t ξ (p ^ n) →* Kˣ, ∃ h : Fin g → A, ∀ (R : Type) [CommRing R] (φ : A →+* R) (u : R →+* K) (x : Sp R ⟶ X) (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X) (c : TorsChar t z (p ^ n)), u.comp φ = algebraMap A K → spMap φ ≫ x₀ = x → IsLocalHom ψ → spMap ψ ≫ x = z → InducedBy χ x u ψ c → DlogIs t p n c (fun i => spMap (dualMap (ψ.comp φ)) ≫ e i) (fun i => ψ (φ (h i))) := by
  intro E _ _ _ H X _ t K _ _ ξ p _ n hsK A _ _ _ _ _ x₀ hξ g e he χ
  subst hξ
  have hp : p.Prime := Fact.out
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : CharZero A := ⟨fun a b hab => Nat.cast_injective (R := K) (by rw [← map_natCast (algebraMap A K), hab, map_natCast])⟩
  let eK : FractionRing A →+* K := (FractionRing.algEquiv A K).toRingEquiv.toRingHom
  let eK' : K →+* FractionRing A := (FractionRing.algEquiv A K).symm.toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap A (FractionRing A)) = algebraMap A K :=
    RingHom.ext fun a => (FractionRing.algEquiv A K).commutes a
  have heK' : eK'.comp (algebraMap A K) = algebraMap A (FractionRing A) :=
    RingHom.ext fun a => (FractionRing.algEquiv A K).symm.commutes a
  have hs : SplitTors t x₀ (p ^ n) := by
    intro Ω _ io w hw
    have e₀ : 𝟙 _ ≫ spMap (io.comp (algebraMap A (FractionRing A))) ≫ x₀ = spMap (io.comp eK') ≫ spMap (algebraMap A K) ≫ x₀ := by
      rw [Category.id_comp, spc_assoc, RingHom.comp_assoc, heK']
    obtain ⟨w₀, h₀⟩ := hsK Ω (io.comp eK') (pull _ e₀ w) (by rw [← map_pow, hw, map_one])
    refine ⟨spMap eK' ≫ w₀, ?_⟩
    rw [spc_assoc, h₀, pull_left, Category.id_comp]
  have hF : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → ∃ P : FP t x₀ (p ^ n), P.Full 𝔮 := fun 𝔮 h𝔮 => ex_full hq hs 𝔮 h𝔮
  have e₁ : spMap eK ≫ spMap (algebraMap A (FractionRing A)) ≫ x₀ = spMap (algebraMap A K) ≫ x₀ := by
    rw [spc_assoc, heK]
  let j : Gam t x₀ (p ^ n) →* TorsK t (spMap (algebraMap A K) ≫ x₀) (p ^ n) :=
    ((pull _ e₁).comp (Gam t x₀ (p ^ n)).subtype).codRestrict _ fun a => by
      show pull _ e₁ a.1 ^ p ^ n = 1
      rw [← map_pow, show a.1 ^ p ^ n = 1 from a.2, map_one]
  have hroot : ∀ z : Kˣ, z ^ p ^ n = 1 → ∃ v : Aˣ, Units.map (algebraMap A K).toMonoidHom v = z := by
    intro z hz
    have hint : ∀ y : K, y ^ p ^ n = 1 → ∃ r : A, algebraMap A K r = y := fun y hy =>
      IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [hy]; exact isIntegral_one))
    obtain ⟨r, hr⟩ := hint z (by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
    obtain ⟨r', hr'⟩ := hint (↑z⁻¹) (by rw [← Units.val_pow_eq_pow_val, inv_pow, hz, inv_one, Units.val_one])
    have h1 : r * r' = 1 := IsFractionRing.injective A K (by rw [map_mul, hr, hr', Units.mul_inv, map_one])
    exact ⟨⟨r, r', h1, by rw [mul_comm, h1]⟩, Units.ext hr⟩
  choose v hv using fun a : Gam t x₀ (p ^ n) => hroot (χ (j a)) (by
    rw [← map_pow, ← map_pow, show a ^ p ^ n = 1 from Subtype.ext a.2, map_one, map_one])
  let χ' : Gam t x₀ (p ^ n) →* Aˣ := MonoidHom.mk' v fun a b =>
    Units.map_injective (f := (algebraMap A K).toMonoidHom) (IsFractionRing.injective A K)
      (by rw [map_mul, hv, hv, hv, map_mul, map_mul])
  obtain ⟨h, hh⟩ := ex_dlog hF (mult_kap χ') he
  refine ⟨h, fun R _ φ u x ψ z c hu hx hψ hz hind => ?_⟩
  subst hx
  obtain rfl : z = spMap (ψ.comp φ) ≫ x₀ := hz.symm.trans (spc_assoc _ _ _)
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  obtain ⟨P, hP⟩ := hF ((IsLocalRing.maximalIdeal _).comap (ψ.comp φ)) inferInstance
  obtain ⟨b, hb⟩ := P.ex_gl (mult_kap χ')
  obtain ⟨c', hc'⟩ := ex_char hP hb
  refine dlog_congr (c' := c') (fun i => GlobalTheory.FactorDepth.isTanAtG_map t (ψ.comp φ) (he i))
    (GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t ℂ_[p] _ _ hq c c' fun w hw => ?_) (hh _ (ψ.comp φ) P b hP hb c' hc')
  obtain ⟨β, hβ⟩ := hP.at_fin _ w hw
  refine Units.ext ((hc' _ w β hβ).symm ▸ ?_)
  have hun : IsUnit (φ P.f) := IsUnit.of_map ψ _ hβ.unit
  obtain ⟨φ', hφ'⟩ := FP.ex_lift hun
  have e₂ : ((algebraMap ↥(intO ℂ_[p]) (FractionRing ↥(intO ℂ_[p]))).comp (ψ.comp φ')).comp (algebraMap A (Localization.Away P.f)) =
      (algebraMap ↥(intO ℂ_[p]) (FractionRing ↥(intO ℂ_[p]))).comp ((algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])).comp (ψ.comp φ)) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hφ']; rfl
  have hβK := hβ.map (algebraMap ↥(intO ℂ_[p]) (FractionRing ↥(intO ℂ_[p])))
  rw [← e₂] at hβK
  obtain ⟨σ, hσ⟩ := FP.At.sect hβK
  obtain rfl : β = (ψ.comp φ').comp σ.toRingHom := RingHom.ext fun z =>
    IsFractionRing.injective _ (FractionRing ↥(intO ℂ_[p])) (RingHom.congr_fun hσ z)
  have hR := (P.at_sect σ).map φ'
  rw [hφ'] at hR
  let σR : Over.mk (spMap φ ≫ x₀) ⟶ t.G := mkPt _ hR.over
  have htR : σR ^ p ^ n = 1 := FP.At.tors (w := σR) hR
  have e₃ : spMap u ≫ spMap φ ≫ x₀ = spMap (algebraMap A K) ≫ x₀ := by rw [spc_assoc, hu]
  let k : TorsK t (spMap (algebraMap A K) ≫ x₀) (p ^ n) := ⟨pull _ e₃ σR, by
    show pull _ e₃ σR ^ p ^ n = 1
    rw [← map_pow, htR, map_one]⟩
  let gF : Gam t x₀ (p ^ n) := ⟨mkPt _ (P.at_sectK σ).over, by
    show mkPt _ (P.at_sectK σ).over ^ p ^ n = 1
    exact FP.At.tors (w := mkPt _ (P.at_sectK σ).over) (P.at_sectK σ)⟩
  have huφ : u.comp φ' = eK.comp P.toK := IsLocalization.ringHom_ext (Submonoid.powers P.f) (by
    rw [RingHom.comp_assoc, hφ', hu, RingHom.comp_assoc, P.toK_comp, heK])
  have hk : j gF = k := Subtype.ext (Over.OverMorphism.ext (by
    show spMap eK ≫ spMap (P.toK.comp σ.toRingHom) ≫ P.u.left = spMap u ≫ spMap φ' ≫ spMap σ.toRingHom ≫ P.u.left
    rw [spc_assoc (P.toK.comp σ.toRingHom) eK P.u.left, spc_assoc σ.toRingHom φ' P.u.left,
      spc_assoc (φ'.comp σ.toRingHom) u P.u.left, ← RingHom.comp_assoc, ← RingHom.comp_assoc, huφ]))
  have h3 := hb.1 _ _ (P.at_sectK σ)
  have h4 : HTMap.kap χ' (spMap (P.toK.comp σ.toRingHom) ≫ P.u.left) = χ' gF := kap_left χ' gF
  rw [h4] at h3
  refine hind σR k (φ' (σ b)) w htR rfl ?_ ?_
  · rw [mkPt_left, ← hβ.2, spc_assoc σ.toRingHom φ' P.u.left, spc_assoc (φ'.comp σ.toRingHom) ψ P.u.left,
      RingHom.comp_assoc]
  · have h5 : u (φ' (σ b)) = eK (P.toK (σ b)) := RingHom.congr_fun huφ _
    rw [h5, ← hk]
    have h6 := congrArg eK h3
    rw [← RingHom.comp_apply eK (algebraMap A _), heK] at h6
    refine (RingHom.congr_fun rfl _).trans (h6.trans ?_)
    exact congrArg Units.val (hv gF)

end GlobalTheory.HtGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedGenericExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.HTLocWeil

theorem unit_of_root {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {N : ℕ} (hN : 0 < N)
    (c : Γ(Sp (FractionRing R), ⊤)ˣ) (hc : c ^ N = 1) :
    ∃ u : Rˣ, unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = c := by
  let c' : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c
  have hc' : c' ^ N = 1 := by rw [← map_pow, hc, map_one]
  have hint : ∀ x : (FractionRing R)ˣ, x ^ N = 1 → ∃ r : R, algebraMap R (FractionRing R) r = x := fun x hx => by
    have : IsIntegral R (x : FractionRing R) := IsIntegral.of_pow hN (by
      rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]; exact isIntegral_one)
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  obtain ⟨r, hr⟩ := hint c' hc'
  obtain ⟨r', hr'⟩ := hint c'⁻¹ (by rw [inv_pow, hc', inv_one])
  have h1 : r * r' = 1 := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, hr, hr', map_one, Units.mul_inv])
  refine ⟨⟨r, r', h1, by rw [mul_comm, h1]⟩, ?_⟩
  have : Units.map (algebraMap R (FractionRing R)).toMonoidHom ⟨r, r', h1, by rw [mul_comm, h1]⟩ = c' := Units.ext hr
  rw [this]
  ext : 1
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom (c : Γ(Sp (FractionRing R), ⊤))) = c
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

theorem unitOn_inj {R : Type} [CommRing R] {u v : Rˣ} (h : unitOn u = unitOn v) : u = v := by
  ext : 1
  have := congrArg (fun z : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z : Γ(Sp R, ⊤))) h
  simpa [unitOn, ← CommRingCat.comp_apply] using this

end GlobalTheory.HTLocWeil

namespace GlobalTheory.HTLocWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
  {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype)
  {T : Scheme.{0}} (y : T ⟶ Xo'.XF c')

theorem lift_ex (w : Over.mk (y ≫ Y.j) ⟶ Y.t.G) : ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w.left :=
  ⟨Over.homMk (Y.m.cart.1.lift w.left y (Over.w w)) (Y.m.cart.1.lift_snd _ _ _), Y.m.cart.1.lift_fst _ _ _⟩

variable {Y y}

theorem lift_uniq {σ σ' : Over.mk y ⟶ Y.oF.t.G} (h : σ.left ≫ Y.m.φ = σ'.left ≫ Y.m.φ) : σ = σ' :=
  Over.OverMorphism.ext (Y.m.cart.1.hom_ext h (by rw [Over.w σ, Over.w σ']))

theorem mul_map {σ σ' : Over.mk y ⟶ Y.oF.t.G} {w w' : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ)
    (h' : w'.left = σ'.left ≫ Y.m.φ) : (w * w').left = (σ * σ').left ≫ Y.m.φ :=
  Y.m.cart.2 (Over.mk y) σ σ' w w' h h'

theorem one_map : (1 : Over.mk (y ≫ Y.j) ⟶ Y.t.G).left = (1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ := by
  let z : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk ((1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ) (by
    rw [Category.assoc, Y.m.cart.1.w, ← Category.assoc, Over.w (1 : Over.mk y ⟶ Y.oF.t.G)]; rfl)
  have hz : (z * z).left = z.left := by
    rw [mul_map (σ := 1) (σ' := 1) rfl rfl, _root_.mul_one]; rfl
  have : z = 1 := by
    have e : z * z = z * 1 := by rw [_root_.mul_one]; exact Over.OverMorphism.ext hz
    exact mul_left_cancel e
  rw [← this]; rfl

theorem pow_map {σ : Over.mk y ⟶ Y.oF.t.G} {w : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ) (k : ℕ) :
    (w ^ k).left = (σ ^ k).left ≫ Y.m.φ := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact one_map
  | succ k ih => rw [pow_succ, pow_succ]; exact mul_map ih h

theorem tors_lift {σ : Over.mk y ⟶ Y.oF.t.G} {w : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ) {k : ℕ}
    (hw : w ^ k = 1) : σ ^ k = 1 :=
  lift_uniq (by rw [← pow_map h, hw, one_map])

end GlobalTheory.HTLocWeil

namespace GlobalTheory.HTLocWeil

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) (a : Dw.La)
    (k : ℕ) : Y.oF.etaA a ^ k = Y.oF.etaA (k • a) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul]
    have := Y.oF.etaA_ker 0
    rw [smul_zero] at this
    exact this.symm
  | succ k ih => rw [pow_succ, ih, succ_nsmul, Y.oF.etaA_add]

theorem weil_kappa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n hA R _ _ _ ξ y hy a
  classical
  have hN : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  let P : Out.PolAV (Xo'.XF c') := GlobalTheory.Obj.toPolAV Y.oF
  have hG := GlobalTheory.laws_without_cohomology.1
  let e0 : Over.mk y ⟶ Y.oF.t.G := toUnit (Over.mk y) ≫ Y.oF.etaA a
  have he0 : e0 ^ (p ^ n) = 1 := by
    show (toUnit (Over.mk y) ≫ Y.oF.etaA a) ^ (p ^ n) = 1
    rw [← MonObj.comp_pow, etaA_pow, ← hA, Y.oF.etaA_ker, MonObj.comp_one]
  let good : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ → Prop := fun w u =>
    ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w ∧ σ ^ (p ^ n) = 1 ∧
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u))
  let κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ := fun w => if h : ∃ u, good w u then h.choose else 1

  have ex : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∃ u, good (σ.left ≫ Y.m.φ) u := fun σ hσ => by
    obtain ⟨c, hc, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ
    obtain ⟨u, hu⟩ := unit_of_root hN c (GlobalTheory.TorsCoord.pow_eq_one_of_weilIs hG P hc he0)
    exact ⟨u, σ, rfl, hσ, hu ▸ hc⟩
  have val : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 →
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := fun σ hσ => by
    have h := ex σ hσ
    have hk : κ (σ.left ≫ Y.m.φ) = h.choose := dif_pos h
    obtain ⟨σ', e1, -, h2⟩ := h.choose_spec
    rw [hk]
    exact (lift_uniq e1) ▸ h2
  have uniq : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∀ u v : Rˣ,
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u)) →
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) → u = v := fun σ hσ u v hu hv => by
    have := (GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ).unique hu hv
    have := unitOn_inj this
    ext : 1
    exact IsFractionRing.injective R (FractionRing R) (congrArg Units.val this)
  refine ⟨κ, fun w w' hw hw' => ?_, fun e σ he hσ => ?_⟩
  ·
    have hwy : ∀ v : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ ξ) ⟶ Y.t.G,
        v.left ≫ Y.t.G.hom = y ≫ Y.j := fun v => by rw [Over.w v]; exact hy
    let w₁ : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk w.left (hwy w)
    let w₁' : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk w'.left (hwy w')
    obtain ⟨σ, hσ⟩ := lift_ex Y y w₁
    obtain ⟨σ', hσ'⟩ := lift_ex Y y w₁'
    have t1 : σ ^ (p ^ n) = 1 := tors_lift hσ.symm (HTMap.tors_of (g := 𝟙 _)
      (show w₁.left = 𝟙 _ ≫ w.left from (Category.id_comp _).symm) hw)
    have t2 : σ' ^ (p ^ n) = 1 := tors_lift hσ'.symm (HTMap.tors_of (g := 𝟙 _)
      (show w₁'.left = 𝟙 _ ≫ w'.left from (Category.id_comp _).symm) hw')
    have t3 : (σ * σ') ^ (p ^ n) = 1 := by rw [mul_pow, t1, t2, _root_.one_mul]
    have hm : (w * w').left = (σ * σ').left ≫ Y.m.φ := by
      rw [HTMap.mul_of (g := 𝟙 _) (w₁ := w₁) (w₂ := w₁') (w₁' := w) (w₂' := w') (Category.id_comp _).symm (Category.id_comp _).symm,
        Category.id_comp]
      exact mul_map hσ.symm hσ'.symm
    have v1 := val σ t1
    have v2 := val σ' t2
    rw [hσ] at v1
    rw [hσ'] at v2
    have v3 := val (σ * σ') t3
    rw [← hm] at v3
    have sk := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk y)).1
    have v4 := sk _ _ _ (GlobalTheory.weilIs_mul_left hG _ P (p ^ n) (Over.mk y) σ σ' e0 _ _ (sk _ _ _ v1) (sk _ _ _ v2))
    refine uniq _ t3 _ _ v3 ?_
    have ceq : unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left * κ w'.left)) =
        ((unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left)))⁻¹ *
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w'.left)))⁻¹)⁻¹ := by
      simp only [mul_inv, inv_inv, unitOn, map_mul]
    rw [ceq]
    exact v4
  · have he' : e = e0 := Over.OverMorphism.ext (by
      rw [he]; show _ = (toUnit (Over.mk y)).left ≫ _; congr 1)
    rw [he']
    exact val σ hσ

end GlobalTheory.HTLocWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleFibre

theorem isAmpleLB_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  intro k _ X _ p D hX L A hL hA l _
  haveI := hX.finite
  have hc := GlobalTheory.NefFibPrime.isClosedImmersion_spMap_zmod l
  haveI : IsClosedImmersion (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip hc
  set f := Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hf
  set g := Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hg
  letI := GlobalTheory.algebraΓOfHom g
  have hproj : IsProjOver g := by
    have h := GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l f
    rwa [GlobalTheory.strHom_eq (f := g) fun _ => rfl] at h
  have hN : IsNef (ZMod l) (L.B.pull f) :=
    GlobalTheory.FibreNef.isNef_pull_of_nefOver l f L ((GlobalTheory.VertForm.nefFib_iff L).1 hL l Fact.out)
  have hAf : IsAmpleLB (A.B.pull f) := hA.pull_of_isClosedImmersion f
  have hK := IsAmpleLB.tens_of_isNef GlobalTheory.nefNumerics_outright (ZMod l) _ g hproj _ _ hAf hN
  refine hK.of_lbIso (LB.isLB_pull (L.tens A).isLB f) ?_
  refine (CechPic.cls_eq_iff (LB.isLB_pull (L.tens A).isLB f)
    (CechPic.isLB_tens (LB.isLB_pull A.isLB f) (LB.isLB_pull L.isLB f))).1 ?_
  show CechPic.pull f (CechPic.cls L.B L.isLB + CechPic.cls A.B A.isLB) =
    CechPic.pull f (CechPic.cls A.B A.isLB) + CechPic.pull f (CechPic.cls L.B L.isLB)
  rw [map_add, add_comm]

end GlobalTheory.AmpleFibre
end
end

