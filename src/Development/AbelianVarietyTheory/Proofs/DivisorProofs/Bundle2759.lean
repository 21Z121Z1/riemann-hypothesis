import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RefTauCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem gm_stalk {X Y Z : Scheme.{0}} (κ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  refine (gm_val (κ ≫ r) z U h a).trans (Eq.trans ?_ (congrArg (κ.stalkMap z).hom (gm_val r (κ z) U h a)).symm)
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : Z ⟶ Y) (r : Y ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    val t (κ ≫ r) z J = Units.map (κ.stalkMap z).hom.toMonoidHom (val t r (κ z) fun ψ => J (κ ≫ ψ)) := by
  rw [val_of t (κ ≫ r) z J (fun k => J (κ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalk κ r z _ (Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)) _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_good_over (ξ : Spec (CommRingCat.of (FractionRing R))) {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ S) [IsSeparated s] (f : Spec (CommRingCat.of R) ⟶ S) :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = f →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = f})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem gm_unitOn {A : Type} [CommRing A] (σ : A →+* FractionRing R) (ξ : Spec (CommRingCat.of (FractionRing R)))
    (k : Aˣ) : (gm (spMap σ) ξ ⊤ (unitOn k)).val = kst ξ (σ k) := by
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) k.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact (congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  intro R _ _ R' _ _ _ Q ρ D e hρ href a b k hk x hx
  letI := D.P.isAb.comm
  obtain ⟨β, β₂, w, h₁, h₂, -, -, h₅⟩ := href
  have hσ : ∀ r, IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (ρ r) := fun r => IsFractionRing.lift_algebraMap _ r
  generalize IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) = σ at hσ ⊢
  have hκ : spMap σ ≫ jK R = jK R' ≫ spMap ρ := by
    have : σ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := RingHom.ext hσ
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  obtain ⟨J, hJ, hc⟩ := exists_good_over ξ Q.M.isLB Q.B.hom (spMap ρ)
  have E := h₅ (spMap σ) hκ a b ξ J J' hJ hJ'
  obtain ⟨u₁, e₁⟩ := GlobalTheory.TauShift.coord_val D ξ hJ' hc' hx
  obtain ⟨u₂, e₂⟩ : ∃ u : R'ˣ, (lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ξ J J').val =
      cst ξ u := by
    have hp : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left = jK R' ≫ (lift (D.c a) (D.c b)).left := by
      simp [← CartesianMonoidalCategory.comp_lift]
    rw [hp]
    refine unit_gm' ξ (lift (D.c a) (D.c b)).left _ ?_ _
    refine And.intro (mem_pull.2 (Set.mem_iInter.2 fun I => ?_)) (Set.mem_iInter.2 fun I => ?_)
    · have := hc ((lift (D.c a) (D.c b)).left ≫ β₂ ≫ (psum Q.B (x2 Q.B) I.down).left) (by
        rw [Category.assoc, Category.assoc, Over.w, ← Over.w (fst Q.B Q.B), reassoc_of% h₂.1, h₁.1.w,
          Over.w_assoc, Over.w_assoc]
        exact Category.id_comp _)
      exact this
    · have := hc' ((lift (D.c a) (D.c b)).left ≫ (psum D.P.A (x2 D.P.A) I.down).left) (by
        rw [Category.assoc, Over.w, Over.w]; rfl)
      exact this
  obtain ⟨u, -, hu⟩ := hk
  obtain ⟨u₃, e₃⟩ : ∃ v : R'ˣ, (val u (jK R' ≫ spMap ρ) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun i => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B, lamPts (Q.c (e a)) (Q.c (e b)) i = q.left := by
      fin_cases i <;> exact ⟨_, rfl⟩
    have := hc (spMap ρ ≫ lamPts (Q.c (e a)) (Q.c (e b)) i) (by
      rw [hq, Category.assoc, Over.w q]; exact Category.comp_id _)
    exact this
  have hT := congrArg (Units.map ((spMap σ).stalkMap ξ).hom.toMonoidHom)
    (hu (spMap σ ξ) (fun ψ => J (spMap σ ≫ ψ)) fun ψ => hJ (spMap σ ≫ ψ))
  have v₁ := val_stalk (Q.tau (e a) (e b)) (spMap σ) (𝟙 (TK R).left) ξ hJ
  have v₂ := val_stalk u (spMap σ) (toUnit (TK R)).left ξ hJ
  have v₃ := gm_stalk (spMap σ) (𝟙 (TK R).left) ξ ⊤ trivial (unitOn k)
  have hh : spMap σ ≫ (toUnit (TK R)).left = jK R' ≫ spMap ρ := by
    rw [show (toUnit (TK R)).left = jK R by simpa using Over.w (toUnit (TK R))]; exact hκ
  have hT' := v₁.trans (hT.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) v₃.symm v₂.symm)))
  rw [hh] at hT'
  rw [show spMap σ ≫ 𝟙 (TK R).left = spMap σ from Category.comp_id _] at hT'
  have F : (val (Q.tau (e a) (e b)) (spMap σ) ξ J).val = kst ξ (σ k) * cst ξ u₃ :=
    (congrArg Units.val hT').trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (gm_unitOn σ ξ k) e₃))
  have G : kst ξ x.val = cst ξ u₁ * (cst ξ u₂ * (kst ξ (σ k) * cst ξ u₃)) :=
    (congrArg Units.val e₁).trans ((Units.val_mul _ _).trans (congrArg (cst ξ u₁ * ·)
      ((congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) e₂ F)))))
  refine ⟨u₁ * u₂ * u₃, kst_injective ξ ?_⟩
  rw [G, map_mul, kst_algebraMap, Units.val_mul, Units.val_mul, map_mul, map_mul]
  ring

end GlobalTheory.RefTauCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.DetHT

namespace GlobalTheory.DetHT.RegLoc

theorem mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (c : Γ(X, U)) :
    x ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    change hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  rwa [hU.fromSpec_primeIdealOf] at h₂

theorem eval_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (κ : Γ(X, U) →+* R) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (((Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec).appLE U ⊤ h) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom s = κ s := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have e1 : (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom κ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have e2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom κ)).appTop =
      CommRingCat.ofHom κ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom κ)).symm
  rw [e1, e2, e3]
  simp

theorem ideal_ne_top {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (hN : IsIntegrallyClosed (X.presheaf.stalk x)) {𝔪 : Ideal Γ(X, U)} (h𝔪 : 𝔪 ≠ ⊤)
    (hP : (hU.primeIdealOf ⟨x, hx⟩).asIdeal ≤ 𝔪) {g : X.functionField} (hg : g ≠ 0) (hreg : ¬ RegAt x g) :
    𝔪.map (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) {g⁻¹})) ⊔
      Ideal.span {(⟨g⁻¹, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin Γ(X, U) {g⁻¹})} ≠ ⊤ := by
  intro heq
  letI := invertibleOfNonzero (inv_ne_zero hg)
  obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top g⁻¹ 𝔪 h𝔪 heq
  rw [invOf_eq_inv, inv_inv] at hpx
  have hlc : p.leadingCoeff ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun h =>
    h𝔪 ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (hP h) hp))
  have hu : IsUnit (X.presheaf.germ U x hx p.leadingCoeff) :=
    (X.mem_basicOpen _ _ hx).1 ((mem_basicOpen_iff hU hx _).2 hlc)
  have hgm : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) =
      algebraMap Γ(X, U) X.functionField a := fun a => algebraMap_germ hx a
  let q := p.map (X.presheaf.germ U x hx).hom
  have hq : Polynomial.aeval g q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    convert hpx using 1
    rw [Polynomial.aeval_def]
    congr 1
    ext a
    exact hgm a
  have hlq : q.leadingCoeff = X.presheaf.germ U x hx p.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero
  have hint : IsIntegral (X.presheaf.stalk x) g := by
    refine ⟨Polynomial.C (hu.unit⁻¹ : (X.presheaf.stalk x)ˣ).1 * q,
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlq]; simp), ?_⟩
    rw [← Polynomial.aeval_def, map_mul, hq, mul_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk x) (K := X.functionField)).1 hint
  exact hreg ⟨y, hy⟩

theorem valAt_chart {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {K : Type} [Field K]
    (κ : Γ(X, U) →+* K) (s : Γ(X, U)) :
    RegAt (below (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec)) (algebraMap Γ(X, U) X.functionField s) ∧
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) (algebraMap Γ(X, U) X.functionField s) = κ s := by
  have ht : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ⁻¹ᵁ U := fun x _ =>
    (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩
  have hb : below (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ∈ U := ht trivial
  refine ⟨⟨_, algebraMap_germ hb s⟩, ?_⟩
  rw [← eval_fromSpec hU κ ht s, ← OfModel.valAt_fnOf _ hb ht]
  rfl

theorem valAt_div {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {K : Type} [Field K]
    (κ : Γ(X, U) →+* K) (a b : Γ(X, U)) (hb : κ b ≠ 0) {g : X.functionField}
    (hg : g * algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) g * κ b = κ a := by
  set y : Sp K ⟶ X := Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec with hy
  obtain ⟨⟨b', hb'⟩, hvb⟩ := valAt_chart hU κ b
  obtain ⟨⟨a', ha'⟩, hva⟩ := valAt_chart hU κ a
  rw [← hy] at hvb hva
  have hb1 : (Scheme.stalkClosedPointTo y).hom b' = κ b := by rw [← hvb, ← hb', Base.valAt_stalk]
  have ha1 : (Scheme.stalkClosedPointTo y).hom a' = κ a := by rw [← hva, ← ha', Base.valAt_stalk]
  have hu : IsUnit b' := (isUnit_map_iff (Scheme.stalkClosedPointTo y).hom b').1 (by rw [hb1]; exact hb.isUnit)
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hg' : g = algebraMap _ X.functionField (a' * c) := by
    rw [map_mul, ha', ← hg, ← hb', mul_assoc, ← map_mul, hc, map_one, mul_one]
  rw [hg', Base.valAt_stalk, ← hb1, ← ha1, ← map_mul, mul_assoc, mul_comm c, hc, mul_one]

theorem place_eq {F : Type} [Field F] [NumberField F] {v v' : HeightOneSpectrum (𝓞 F)} (e : Ext v')
    (h : ∀ a ∈ v.asIdeal, ∃ c : e.O, (c : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F a) ∧ ¬ IsUnit c) :
    v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := fun a ha => by
    obtain ⟨c, hc, hu⟩ := h a ha
    have h1 : e.w c < 1 := not_le.1 fun h' => hu (RegCrit.isUnit_of_one_le e c h')
    rw [hc, e.w_alg] at h1
    rw [← FinitePlace.norm_lt_one_iff_mem F v' a, FinitePlace.norm_embedding]
    exact h1
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle).symm

theorem exists_hom (F : Type) [Field F] [NumberField F] (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (hinj : Function.Injective (algebraMap A K)) [Algebra (𝓞 F) A] [Algebra.FiniteType (𝓞 F) A] [CharZero A]
    (𝔪 : Ideal A) (t : K)
    (hne : 𝔪.map (algebraMap A (Algebra.adjoin A {t})) ⊔
      Ideal.span {(⟨t, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {t})} ≠ ⊤) (c : A) (hc : c ≠ 0) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : A →+* e.O) (τ : e.O),
      (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) A a) : e.O) : AlgebraicClosure F) =
        algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (∀ m ∈ 𝔪, ¬ IsUnit (φ m)) ∧ φ c ≠ 0 ∧ ¬ IsUnit τ ∧
      ∀ a b : A, t * algebraMap A K a = algebraMap A K b → τ * φ a = φ b := by
  let B := Algebra.adjoin A {t}
  have hB : Function.Injective (algebraMap A B) := fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra (𝓞 F) B := ((algebraMap A B).comp (algebraMap (𝓞 F) A)).toAlgebra
  have : IsScalarTower (𝓞 F) A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Algebra.FiniteType A B := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)
  have : Algebra.FiniteType (𝓞 F) B := Algebra.FiniteType.trans (S := A) inferInstance h1
  have : CharZero B := charZero_of_injective_algebraMap hB
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F B 𝔫 h𝔫 (algebraMap A B c) fun h => hc (hB (by rw [h, map_zero]))
  have hn : ∀ s ∈ 𝔫, ¬ IsUnit (φ s) := fun s hs => by
    rw [← h₂] at hs
    exact hs
  refine ⟨v, e, φ.comp (algebraMap A B), φ ⟨t, Algebra.subset_adjoin rfl⟩, h₁,
    fun m hm => hn _ (hle (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hm))), h₃,
    hn _ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))), fun a b hab => ?_⟩
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  exact congrArg φ (Subtype.ext hab)

open GlobalTheory.TrueGeo.HorizPt in

theorem main : RegLocSt := by
  intro F _ _ Y V U₀ W hW v g hf x hx hxv
  by_contra hreg
  have hg0 : g ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : U ≤ U₀ := hUW
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  have := functionField_isFractionRing_of_isAffineOpen V.X U hU
  obtain ⟨w, hw⟩ := hW
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le ⟨_, gen_mem hw⟩ (gen_mem hxU)
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hh
    exact hh
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(V.X, U)) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj := IsFractionRing.injective Γ(V.X, U) V.X.functionField
  have hb1 : algebraMap Γ(V.X, U) V.X.functionField b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  have hgb : g * algebraMap Γ(V.X, U) V.X.functionField b = algebraMap Γ(V.X, U) V.X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb1]
  obtain ⟨v', e, φ, τ, h₁, h₂, h₃, h₄, h₅⟩ := exists_hom F Γ(V.X, U) V.X.functionField hinj 𝔪 g⁻¹
    (ideal_ne_top hU hxU (V.normal x).2 h𝔪.ne_top hle' hg0 hreg) (b * h) (mul_ne_zero hb0 hh0)
  obtain rfl : v' = v := place_eq e fun c hc => by
    refine ⟨_, h₁ c, h₂ _ (hle' ?_)⟩
    have hx' : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    have hc' : c ∈ ((hU.fromSpec ≫ V.p) (hU.primeIdealOf ⟨x, hxU⟩)).asIdeal := by
      change c ∈ (V.p (hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩))).asIdeal
      rw [hx', hxv]
      exact hc
    rw [fromSpec_str] at hc'
    exact hc'
  have hτ : τ * φ a = φ b := h₅ a b (by rw [← hgb, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul])
  rw [map_mul] at h₃
  let κ : Γ(V.X, U) →+* AlgebraicClosure F := e.O.subtype.comp φ
  have hκ : ∀ s, φ s ≠ 0 → κ s ≠ 0 := fun s hs h => hs (Subtype.ext h)
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hyt : spMap e.O.subtype ≫ yt = Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec := by
    simp only [yt]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  have hval := hf e (V.pb.lift _ _ hw) yt (V.pb.lift_snd _ _ hw) hy.symm
    (fun x _ => hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)) (by
      rw [hy, hyt]
      refine hhW ?_
      change PrimeSpectrum.comap κ (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen h
      rw [hU.fromSpec_preimage_basicOpen]
      intro h'
      have h'' : κ h ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h'
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h''
      exact hκ h (right_ne_zero_of_mul h₃) h'')
  rw [hy, hyt] at hval
  have hκb := hκ b (left_ne_zero_of_mul h₃)
  have hdiv := valAt_div hU κ a b hκb hgb
  have hτ' : (τ : AlgebraicClosure F) * κ a = κ b := congrArg Subtype.val hτ
  rw [← hdiv, ← mul_assoc] at hτ'
  have hone := congrArg e.w (mul_right_cancel₀ hκb (hτ'.trans (one_mul _).symm))
  rw [map_mul, map_one] at hone
  exact h₄ (RegCrit.isUnit_of_one_le e τ (hone.ge.trans (mul_le_of_le_one_right (e.w.nonneg _) hval)))

end GlobalTheory.DetHT.RegLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCover
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGenCurve

theorem natCast_mem_asIdeal {k : Type} [CommRing k] {X Z : Scheme.{0}} (p : X ⟶ Sp k) (i : Z ⟶ X) (l : ℕ)
    (h : (l : Γ(Z, ⊤)) = 0) (z : Z) : (l : k) ∈ (p (i z)).asIdeal := by
  by_contra hl
  have hm : (i ≫ p) z ∈ (Sp k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (l : k)) := by
    rw [basicOpen_eq_of_affine]
    exact hl
  have := (Scheme.preimage_basicOpen (i ≫ p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (l : k))).le hm
  rw [map_natCast, map_natCast] at this
  erw [h, Scheme.basicOpen_zero] at this
  exact this

theorem topSelf_nonneg_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) {B : LB X} (hB : IsGenerated (B.pull i)) :
    0 ≤ topSelfIntersection κ (B.pull i) 1 := by
  have := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hB.isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

theorem algebraMap_gs {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (gs (𝟙 X) x U a) = fnOf U (gen_mem hx) a := by
  rw [gs_eq (𝟙 X) x U hx]
  exact algebraMap_germ hx a

theorem exists_glue {X Z : Scheme.{0}} [IsReduced Z] (i : Z ⟶ X) (V : Z.Opens) (W : Z → X.Opens)
    (f : ∀ z, Γ(X, W z)) (hz : ∀ z ∈ V, i z ∈ W z) (hWV : ∀ z ∈ V, i ⁻¹ᵁ W z ≤ V)
    (hd : ∀ z₁ ∈ V, ∀ z₂ ∈ V, ∀ y : Z, ∀ (h₁ : i y ∈ W z₁) (h₂ : i y ∈ W z₂),
      ¬ IsUnit (gs (𝟙 X) (i y) (W z₁) (f z₁) - gs (𝟙 X) (i y) (W z₂) (f z₂))) :
    ∃ g : Γ(Z, V), ∀ z ∈ V, gs (𝟙 Z) z V g = gs i z (W z) (f z) := by
  let O : V → Z.Opens := fun z => i ⁻¹ᵁ W z.1
  let a : ∀ z : V, Γ(Z, O z) := fun z => (i.app (W z.1)).hom (f z.1)
  have ga : ∀ (z : V) (y : Z) (hy : y ∈ O z), gs (𝟙 Z) y (O z) (a z) = gs i y (W z.1) (f z.1) := fun z y hy =>
    (gs_pull (𝟙 Z) i y _ hy _).trans (by rw [Category.id_comp])
  have hcov : V ≤ iSup O := fun z hzV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hzV⟩, hz z hzV⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.presheaf O a := by
    intro z₁ z₂
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    have hyO : y ∈ O z₁ ⊓ O z₂ := Z.basicOpen_le _ hy
    have hu := (LBGerm.isUnit_gs_iff (𝟙 Z) y _ hyO _).2 hy
    rw [LBGerm.gs_sub (𝟙 Z) y _ hyO] at hu
    erw [gs_res (𝟙 Z) y inf_le_left hyO, gs_res (𝟙 Z) y inf_le_right hyO] at hu
    rw [ga z₁ y hyO.1, ga z₂ y hyO.2, gs_stalkMap i y _ hyO.1, gs_stalkMap i y _ hyO.2, ← map_sub,
      isUnit_map_iff] at hu
    exact hd z₁.1 z₁.2 z₂.1 z₂.2 y hyO.1 hyO.2 hu
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' O V (fun z => homOfLE (hWV z.1 z.2)) hcov a hcomp
  refine ⟨g, fun z hzV => ?_⟩
  have hzO : z ∈ O ⟨z, hzV⟩ := hz z hzV
  rw [← gs_res (𝟙 Z) z (hWV z hzV) hzO g]
  erw [hg ⟨z, hzV⟩]
  exact ga _ z hzO

theorem nefOver_of_localGen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (R : L.B.ι → X.functionFieldˣ), IsRatSec L.B R → ∀ (l n : ℕ)
    (U : X → X.Opens) (s : X → Fin n → X.functionField), (∀ x, x ∈ U x) →
    (∀ (x : X) (i : L.B.ι) (x₀ : X), x₀ ∈ U x → x₀ ∈ L.B.U i → (l : k) ∈ (p x₀).asIdeal →
      (∀ J, RegAt x₀ (s x J * R i)) ∧ (∃ J, UnitAt x₀ (s x J * R i)) ∧
        ∀ x', x₀ ∈ U x' → ∀ J, ¬ UnitAt x₀ ((s x J - s x' J) * R i)) → NefOver L l := by
  intro k _ X _ p D hX L R hR l n U s hU hloc Z i _ _ κ _ _ _ _ hd
  have hl0 : (l : Γ(Z, ⊤)) = 0 := by
    rw [← map_natCast (algebraMap κ Γ(Z, ⊤)), CharP.cast_eq_zero, map_zero]
  have hZl : ∀ z, (l : k) ∈ (p (i z)).asIdeal := natCast_mem_asIdeal p i l hl0
  have hdata : ∀ (a : L.B.ι) (J : Fin n) (z : Z), ∃ (W : X.Opens) (f : Γ(X, W)), W ≤ U (i z) ⊓ L.B.U a ∧
      (i z ∈ L.B.U a → i z ∈ W) ∧ ∀ h, fnOf W h f = s (i z) J * R a := by
    intro a J z
    by_cases hz : i z ∈ L.B.U a
    · obtain ⟨W, hW, f, hf⟩ := ((hloc (i z) a (i z) (hU _) hz (hZl z)).1 J).exists_fnOf
      refine ⟨W ⊓ (U (i z) ⊓ L.B.U a), resG X inf_le_left f, inf_le_right, fun _ => ⟨hW, hU _, hz⟩, fun h => ?_⟩
      rw [fnOf_resG, hf]
    · exact ⟨⊥, 0, bot_le, fun h => (hz h).elim, fun h => absurd h (by simp)⟩
  choose W f hW hWz hf using hdata
  have hglue : ∀ (j : (L.B.pull i).ι) (J : Fin n), ∃ g : Γ(Z, (L.B.pull i).U j),
      ∀ z ∈ (L.B.pull i).U j, gs (𝟙 Z) z _ g = gs i z (W (j PUnit.unit) J z) (f (j PUnit.unit) J z) := by
    intro j J
    refine exists_glue i _ (fun z => W (j PUnit.unit) J z) (fun z => f (j PUnit.unit) J z)
      (fun z hz => hWz _ _ _ (mem_pull.1 hz)) (fun z _ y hy => mem_pull.2 (hW _ _ _ hy).2)
      (fun z₁ _ z₂ _ y h₁ h₂ hu => ?_)
    have m₁ := hW _ _ _ h₁
    have m₂ := hW _ _ _ h₂
    refine (hloc (i z₁) (j PUnit.unit) (i y) m₁.1 m₁.2 (hZl y)).2.2 (i z₂) m₂.1 J ⟨_, hu, ?_⟩
    rw [map_sub, algebraMap_gs h₁, algebraMap_gs h₂, hf, hf, sub_mul]
  choose g hg using hglue
  have hsec : ∀ (J : Fin n) (y : Z) (j j' : (L.B.pull i).ι), y ∈ (L.B.pull i).U j → y ∈ (L.B.pull i).U j' →
      gs (𝟙 Z) y _ (g j J) =
        (gm (𝟙 Z) y ((L.B.pull i).U j ⊓ (L.B.pull i).U j') ((L.B.pull i).g j j')).val * gs (𝟙 Z) y _ (g j' J) := by
    intro J y j j' hj hj'
    have ha := mem_pull.1 hj
    have ha' := mem_pull.1 hj'
    have hm : i y ∈ L.B.U (j PUnit.unit) ⊓ L.B.U (j' PUnit.unit) := ⟨ha, ha'⟩
    rw [hg j J y hj, hg j' J y hj', gm_pull_g L.B i (𝟙 Z) y j j' hj hj', Category.id_comp, ← gs_unit i y _ hm,
      gs_stalkMap i y _ (hWz _ _ _ ha), gs_stalkMap i y _ (hWz _ _ _ ha'), gs_stalkMap i y _ hm, ← map_mul]
    congr 1
    apply IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField
    rw [map_mul, algebraMap_gs (hWz _ _ _ ha), algebraMap_gs hm, algebraMap_gs (hWz _ _ _ ha'), hf, hf,
      hR _ _ (gen_mem hm)]
    ring
  let t : Fin n → (L.B.pull i).Sec := fun J => LBGerm.secOfGerm (fun j => g j J) (hsec J)
  refine topSelf_nonneg_of_isGenerated hX i κ hd (isGenerated_of_finite t (top_le_iff.1 fun y _ => ?_))
  obtain ⟨a, ha⟩ := exists_chart L.isLB (i y)
  obtain ⟨J, b, hb, e⟩ := (hloc (i y) a (i y) (hU _) ha (hZl y)).2.1
  have hy : y ∈ (L.B.pull i).U (fun _ => a) := mem_pull.2 ha
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨J, (mem_nonzeroLocus_iff_isUnit (t J) hy).2 ?_⟩
  change IsUnit (gs (𝟙 Z) y _ (g (fun _ => a) J))
  rw [hg _ J y hy, gs_stalkMap i y _ (hWz _ _ _ ha)]
  have hb' : b = gs (𝟙 X) (i y) _ (f a J y) :=
    IsFractionRing.injective _ X.functionField (by rw [e, algebraMap_gs (hWz _ _ _ ha), hf])
  exact hb' ▸ hb.map _

end GlobalTheory.HtGenCurve
end
end

