import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3533
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.sabMap_of_same_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → ∀ {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, θ (s k) ≠ 0) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e → Nonempty (SABMap t t₁ (spMap θ)) := by
  intro E _ _ _ H D' l c L R V _ _ _ _ _ _ bR bV t₁ P₁ t P iw θ hθ I _ s ε e₁ e hs h₁ h
  classical

  set f : R := ∏ k, s k with hf
  have hfθ : θ f ≠ 0 := by
    rw [hf, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hs k
  have hdiv : ∀ k, ∃ n : ℕ, s k ∣ f ^ n := fun k =>
    ⟨1, by rw [pow_one, hf]; exact Finset.dvd_prod_of_mem s (Finset.mem_univ k)⟩
  have hpsi := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ h₁ f hdiv
  obtain ⟨t', P', hD, ⟨m⟩, hx, hact⟩ := GlobalTheory.T.exists_linearUniformisation_pullback_localMap R V bR bV t₁ P₁ θ hθ f hfθ hpsi
  let e' : P'.D.toPre.X ≃ₗ[𝓞 E] L.D.X := (hD.xe.toLinearEquiv hx).trans e₁
  have h' := GlobalTheory.T.comesFromBase_stable_under_pullback_of_data L P₁.D.toPre P₁.oD P'.D.toPre P'.oD iw θ s ε e₁ hD e' (fun y => rfl) hact hs h₁
  obtain ⟨hD₂, he₂, hact₂⟩ := GlobalTheory.T.exists_isPullDeg_id_same_coordinates L P'.D.toPre P'.oD P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e' e
    hs h' h
  have hx₂ : ∀ (x : 𝓞 E) y, hD₂.xe (x • y) = x • hD₂.xe y := by
    intro x y
    apply e'.injective
    rw [he₂, map_smul, map_smul, he₂]
  obtain ⟨m₂⟩ := GlobalTheory.T.tripleIso_of_linear_degenerationData_iso V bV t' t P' P hD₂ hx₂ hact₂
  exact GlobalTheory.TraitOrder.comp (Category.id_comp _) m m₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

variable {I : Type}

def FrExp {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  (∃ χ, TorChar 𝔪 τ χ) ∧
  ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
    (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
    (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
    (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧
    (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ w₀.IsGen ∧
    𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s ∧
    (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) ∧ w.IsGen ∧ 𝔪.Over' w₀ g' w (x a) (fr a) ∧
    ∀ χ, TorChar 𝔪 τ χ → ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∀ g'' : GtPtF 𝔪.D.toPre (FractionRing V),
      g'.IsAdd g₀ g'' → ∀ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 g''.b, w''.IsGen →
      (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val =
        cstH (R := V) z (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e))) * (val w'' (𝟙 _) z J).val) →
      𝔪.Over' w₀ g'' w'' (x (a + τ)) (fr (a + τ))

end GlobalTheory.GSep.TransTerms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  first | (exact @GlobalTheory.LKGeo.actG_form_eq_sim) | (exact GlobalTheory.LKGeo.actG_form_eq_sim) | (intros; apply GlobalTheory.LKGeo.actG_form_eq_sim  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReductionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorModuliObject_potentiallyGoodReduction : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.HTPotGood.potGood | exact GlobalTheory.HTPotGood.potGood | (intros; apply GlobalTheory.HTPotGood.potGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFiniteType
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualConFT

theorem hasRep_quot_of_factor {S T : Type} [CommRing S] [CommRing T] (J : Ideal S) (φ : S →+* T)
    (ψ : T →+* S ⧸ J) (hcomp : ψ.comp φ = Ideal.Quotient.mk J) (g : ℕ)
    (h : ∀ (B : Over (Sp T)) [GrpObj B], IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      HasRep B g (𝟙_ _))
    (A : Over (Sp S)) [GrpObj A] (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) := by
  let f : Sp T ⟶ Sp S := spMap φ
  let B : Over (Sp T) := (Over.pullback f).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback φ A B _ g hB hA hg
  have h2 := (GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ f A B _ hB g (𝟙_ _)).1.mp (h B hAB hgB)
  refine GlobalTheory.T.baseChangeBis _ A (Over.mk ((𝟙_ (Over (Sp T))).hom ≫ f)) (Over.mk (spMap (Ideal.Quotient.mk J))) g
    (Over.homMk (spMap ψ) ?_) h2
  change spMap ψ ≫ 𝟙 _ ≫ spMap φ = spMap (Ideal.Quotient.mk J)
  rw [Category.id_comp, ← hcomp, spMap_comp]

end GlobalTheory.DualConFT

namespace GlobalTheory.DualConFT

theorem hasRep_quot (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (g : ℕ) (I : Ideal R) :
    ∀ (A : Over (Sp (R ⧸ I))) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      HasRep A g (𝟙_ _) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  induction I using WellFoundedGT.induction with
  | _ I ih =>
    intro A _ hA hg
    haveI : @Algebra.FiniteType ℤ (R ⧸ I) _ _ (Ring.toIntAlgebra _) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective
    refine GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction (R ⧸ I) A g hA hg fun J' hJ' => ?_
    let J : Ideal R := J'.comap (Ideal.Quotient.mk I)
    have hle : I ≤ J := fun a ha => by
      show Ideal.Quotient.mk I a ∈ J'
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact J'.zero_mem
    have hlt : I < J := by
      refine lt_of_le_of_ne hle fun hIJ => hJ' ?_
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have ha : a ∈ J := hx
      rw [← hIJ] at ha
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact (⊥ : Ideal (R ⧸ I)).zero_mem
    let ψ : R ⧸ J →+* (R ⧸ I) ⧸ J' :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk J').comp (Ideal.Quotient.mk I)) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
    refine hasRep_quot_of_factor J' (Ideal.Quotient.factor hle) ψ ?_ g (fun B _ hB hgB => ih J hlt B hB hgB)
      A hA hg
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

theorem hasRep_of_finiteType : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg
  refine GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction R A g hA hg fun J _ => ?_
  exact hasRep_quot_of_factor J (Ideal.Quotient.mk J) (RingHom.id _) rfl g
    (fun B _ hB hgB => hasRep_quot R g J B hB hgB) A hA hg

end GlobalTheory.DualConFT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open GlobalTheory.CechPic GlobalTheory.DiagPairing GlobalTheory.HeckeWeilLift

theorem exists_weilIs_heckeA : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∃ v : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) v := by
  intro p _ D R _ b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₂ hg₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) g₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) g₂ t₂⟩)

theorem weilIs_heckeA_pow_eq_one {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]
    {b : Base D R} {s : S ⟶ Sp R} (f : D.La →+ D.La) (c k N : ℕ) (o : Obj b (N * k) s)
    (g₁ : 𝟙_ (Over S) ⟶ o.A) (hg₁ : g₁ ∈ heckeSubA o f N) (g₂ : 𝟙_ (Over S) ⟶ o.A)
    (v : Γ((𝟙_ (Over S)).left, ⊤)ˣ)
    (hv : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)
      (lift 1 g₂) v) : v ^ k = 1 := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hL : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hk1 : g₁ ^ k = 1 := pow_eq_one_of_mem o f g₁ hg₁
  have hxk : (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ k = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.pow_comp]; simp [hk1]
    · rw [MonObj.pow_comp]; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
  have pw : ∀ m : ℕ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1
      ((lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ (m + 1)) (lift 1 g₂) (v ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih =>
      rw [pow_succ _ (m + 1), pow_succ v (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih hv
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hxk] at hp
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL hp hp
  rw [_root_.mul_one] at h11
  exact mul_eq_left.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h11 hp)

theorem weilIs_heckeSubA_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) 1 := by
  intro p _ D R _ b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂
  obtain ⟨v, hv⟩ := exists_weilIs_heckeA p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁
    g₂ hg₂
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : v = 1 := by
    refine GlobalTheory.rootOfUnity_eq_one_of_geom R S s k v (b.unit k hk)
      (weilIs_heckeA_pow_eq_one (h (N * k)) c k N o g₁ hg₁ g₂ v hv) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hv
    exact GlobalTheory.T.hecke_coefficients_congruence_scaled p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂ K x β hx _ hp
  subst h1
  exact hv

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_descent_to_component_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) A φ J d := by
  first | exact @GlobalTheory.UPoincDown.idealDescent | exact GlobalTheory.UPoincDown.idealDescent | (intros; apply GlobalTheory.UPoincDown.idealDescent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdeleUnitCongruenceSequence
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adele_unit_congruence_sequence : ∀ (p : ℕ) [Fact p.Prime] (ε ε' : AfP p), IsIntAf ε → IsIntAf ε' → ε * ε' = 1 → ∃ u : ℕ → ℤ, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ u (n * m) - u n) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
  first | (exact @GlobalTheory.UnitApprox.exists_int_approx) | (exact GlobalTheory.UnitApprox.exists_int_approx) | (intros; apply GlobalTheory.UnitApprox.exists_int_approx  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSquaredThetaTermsTorusCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_squaredThetaTerms_torusCoordinates : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult →
    ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
    (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X)
      (hs : ∀ k, IsUnit (s (.inr k))),
    GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) →
    (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) →
    ∃ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
      (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)))
      (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε))
      (s₀ : V₁) (G : X → C → V₁),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') ∧
      (∀ c, b c ^ N₁ = 1) ∧
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) ∧
      IsUnit s₀ ∧
      (∀ mu c, u mu c ^ 2 * s₀ = ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) * G mu c) ∧
      ∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  first | exact @GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms | exact GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms | (intros; apply GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEndomorphismIntegralApproximation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_endomorphism_integral_approximation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  first | (exact @GlobalTheory.LKGeo.LiftSys.exists_lift_sys) | (exact GlobalTheory.LKGeo.LiftSys.exists_lift_sys) | (intros; apply GlobalTheory.LKGeo.LiftSys.exists_lift_sys  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleThickeningSquareTheoremStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_thickening_square_theorem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  first | exact @GlobalTheory.TowerStep.step | exact GlobalTheory.TowerStep.step | (intros; apply GlobalTheory.TowerStep.step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignatureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_triple_signature : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) W.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ → ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ Φ' ∈ algF ψ θ false A₁ B, p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' = 0 → ∀ Φ'' ∈ algF ψ θ false A₁ B, thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  first | exact @GlobalTheory.DefIrred.vanish_all | exact GlobalTheory.DefIrred.vanish_all | (intros; apply GlobalTheory.DefIrred.vanish_all <;> assumption)
end

