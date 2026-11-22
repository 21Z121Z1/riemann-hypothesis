import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Periods

theorem one_lattice {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (D : DegData R (maximalIdeal R)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)) (P : ∀ T : Trait F, (R →+* T.V) → Prop)
    (h : ∀ T ψ, P T ψ → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧
      ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y))) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), 1 ≤ c ∧ ∀ T ψ, P T ψ →
      ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  have hc : 0 < W 0 0 := by
    have := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  by_cases hex : ∃ T ψ, P T ψ
  swap
  · push_neg at hex
    exact ⟨PUnit, inferInstance, fun _ => 0, 1, le_rfl, fun T ψ hP => absurd hP (hex T ψ)⟩
  obtain ⟨T₀, ψ₀, hP₀⟩ := hex
  obtain ⟨e₀, -, he₀⟩ := h T₀ ψ₀ hP₀
  have hcoord : ∀ z, ∃ r, PsiCoord D.toPre (e₀.symm (Pi.single 0 z)) r := fun z =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre _).2 (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  choose p hp using hcoord
  refine ⟨T₀.D.toPre.X, inferInstance, p, (W 0 0).toNat, by omega, fun T ψ hP => ?_⟩
  obtain ⟨ρT, hρ, hm⟩ := h T ψ hP
  obtain ⟨π, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT.toAddMonoidHom
    ρT.surjective he₀ hm
  have hsingle : ∀ z, ρT (e₀.symm (Pi.single 0 z)) = Pi.single 0 (π z) := by
    intro z
    funext u
    have := hπ (e₀.symm (Pi.single 0 z)) u
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at this
    rw [this]
    by_cases hu : u = 0
    · subst hu; simp
    · simp [Pi.single_apply, hu]
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : ρT (e₀.symm (Pi.single 0 z)) = 0 := by rw [hsingle, hz, Pi.single_zero]
    have h2 : e₀.symm (Pi.single 0 z) = 0 := by simpa using h1
    have h3 : (Pi.single 0 z : Fin 8 → T₀.D.toPre.X) = 0 := by simpa using h2
    simpa using congrFun h3 0
  refine ⟨AddEquiv.ofBijective π ⟨hinj, hπs⟩, fun z => ?_⟩
  obtain ⟨h0, ha⟩ := hρ _ _ (hp z)
  rw [hsingle] at h0 ha
  have hq : qW W T.β (Pi.single 0 (π z)) = W 0 0 * T.β (π z) (π z) := by
    unfold qW
    rw [Finset.sum_eq_single 0 (fun u _ hu => by simp [Pi.single_eq_of_ne hu]) (by simp)]
    rw [Finset.sum_eq_single 0 (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
    simp
  refine ⟨(qW W T.β (Pi.single 0 (π z))).toNat, ?_, ha⟩
  rw [Int.toNat_of_nonneg h0, hq, Int.toNat_of_nonneg hc.le]
  rfl

end GlobalTheory.Poinc.Periods

theorem GlobalTheory.Poinc.Periods.trait_iso : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ M.Z) [IsCommMonObj ((Over.pullback ξ).obj FinalForm.G)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj FinalForm.G)), LBIso U.LG.L (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus FinalForm.G)) → ∀ (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)), (∀ a b, EndChar U ((Over.pullback ξ).map (f a b)) (m a b)) → ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R _ _ _ hB ξ _ D A U hL hP m hm T ψ hl ht
  have hVab := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv).1
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  have hgen : ∀ w, (jK T.V ≫ spMap ψ ≫ ξ) w ∈ abLocus FinalForm.G := by
    obtain ⟨ξ₀, hξ₀, -⟩ := ht
    intro w
    rw [← hξ₀]
    exact hVab (ξ₀ w).2
  obtain ⟨G', _, _, D', A', U', gm, ι, hG', hgm, hLB, hC, hE⟩ :=
    GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus M.Z FinalForm.G FinalForm.semi FinalForm.L.L R hB ξ D A U hL hP T.V hBV ψ hl hgen
  refine GlobalTheory.T.characterGroup_eq_eighthPower_lattice_over_trait g n o ζ F W hW o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R ξ D.toPre m
    T ψ ht G' D' A' U' gm ι hG' hgm hLB hC fun a b => ?_
  obtain ⟨f', hf'm, hf'c, hf'e⟩ := hE (f a b) (hf a b).1
  exact ⟨f', hf'm, hf'c, fun m' hm' => hf'e _ m' (hm a b) hm'⟩

theorem GlobalTheory.Poinc.Periods.main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u hu M U₀ EE FinalForm hO V v hv x
  obtain ⟨c, pr, hs⟩ := (sharpOver_iff F W ρ.P u).1 hu
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  have hB : GlobalTheory.Mum.Base R := ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩
  have hGs : IsSemiAbelian ((Over.pullback ξ).obj FinalForm.G) := IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi
  obtain ⟨hsb, hpr, huniq, hlb⟩ := hs
  choose f hf using matOn_exists o' Ω S ρ M U₀ EE FinalForm hO.ne c.A pr hpr huniq
  have hfm : ∀ a b, IsMonHom ((Over.pullback ξ).map (f a b)) := fun a b => by
    have := (hf a b).1
    infer_instance
  choose m hmc using fun a b => endChar_exists_of_isMonHom R hB _ hGs D A U _ (hfm a b)
  obtain ⟨Λ, _, p, c', hc', hall⟩ := GlobalTheory.Poinc.Periods.one_lattice D W hW m
    (fun T ψ => IsLocalHom ψ ∧ ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x))
    (fun T ψ hT => by
      obtain ⟨hl, ht⟩ := hT
      have e : spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x = spMap ψ ≫ ξ := by
        rw [hξ, ← Category.assoc]
        congr 1
        exact Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      rw [e] at ht
      exact GlobalTheory.Poinc.Periods.trait_iso g n o ζ F W hW o' Ω S ρ u c pr ⟨hsb, hpr, huniq, hlb⟩ M U₀ EE FinalForm hO V v hv f hf R hB ξ
        D A U hL hP m hmc T ψ hl ht)
  exact ⟨R, inferInstance, hRd, hloc, φ, Λ, inferInstance, p, c', hB, isCpl_self _, hc', fun T ψ hl ht => hall T ψ ⟨hl, ht⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEmbeddingCompatibilityRows
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwCx

open GlobalTheory.ExportSeries Formalism.IndefR.Datum GlobalTheory.BigOn.Exp.TupLe GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)

def TwQ : Prop := ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (Q : Finset (Pl D.host.E))
  (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), IntegralHeckeForms.TwOK i k Q ψ → ∀ P ∈ Q, ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

theorem twQ : TwQ := by
  intro D i k Q ψ hok P hP hl
  obtain ⟨-, -, -, -, -, hram, htriv⟩ := hok
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P
  obtain ⟨σ, hσ, hne⟩ := (hram P A hA).2 hP
  exact hne (htriv P hl A hA σ (ReciprocityTheory.Gal.Ine_le_Dec A hσ))

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem cx_at (s1 : PlacesSt) (s2 : FlatSt) (s3 : TraceSt) (s6 : TwQ) (hr : p.Rows) (hm : More p)
    (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) {ν : ℂ} (hfit : Fit p w j hρ ν)
    (hLS : ∀ h, ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h,
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hLI : LatIo p w j)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    (e : FractionRing (ex.nch.Oe w) →+* ℂ)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (z : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w))
    (hz : z ∈ twSet hρ (rdAt p w j hρ ν) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)) :
    ∃ (n : ℕ) (h : Fin n → GA D (Vc D j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → ex.nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : ex.nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc D j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → D.what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) =
        levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((R2 p).vP j ((R2 p).mu (D.plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ (ex.nch.k' w) z = κ • ∑ k, (e (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (a k)) * ν⁻¹) •
        adForm (R2 p) j (y k) (p.v₀ j (sg0 D p.P.A3.A)) := by
  obtain ⟨hadapt, hν, -, hlev⟩ := hfit
  have hpin := hadapt.1
  have hL := GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) :=
    { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin (ex.nch.twI w) j (ex.nch.sd w) with }
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z0, cz, hz0, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z0 ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz0
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨u, hu, hio⟩ := hLI ρ hρ hpin c c0 hs
  obtain ⟨s, h, P, hd, hQ, hsupp, hgen⟩ := hz
  have hq1 := ht.split
  have hq2 : ∀ P' ∈ (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q,
      ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal :=
    fun P' hP' => s6 D _ _ _ _ hok P' (mem_half.1 hP').1
  have hP1 := lat_translate_of_prime hρ _ j _ hq1 hq2 hsupp hd.mem
  have hP2 := lat_translate_of_prime hρ _ j _ p1 p2 (GlobalTheory.DownLift.SplitCoef.suppAt_inv_of hz0) hP1
  have hh2 : h * hQ * z0⁻¹ ∈ GfC (Vc D j) :=
    mul_mem (mul_mem hd.fin (GlobalTheory.TwTraceCx.mem_GfC_of_suppAt hq1 hsupp)) (inv_mem hzf)
  obtain ⟨n', f, g, hsum⟩ := Submodule.mem_span_set'.1 (hLS _ P hP2)
  choose y hy hyio using fun k => hio _ hh2 (g k).1 (g k).2
  choose o ho using fun k => RingHom.mem_range.1 (f k).2
  obtain ⟨uu, huu⟩ := hval (detRoot (Vc D j) (h * hQ))
  have hcu : UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) (cz * (c⁻¹ * ν)) :=
    unitOff_mul hcz (unitOff_root hn (by rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]))
  obtain ⟨-, m, hm1, -⟩ := hcu
  refine ⟨n', fun _ => h * hQ * z0⁻¹, y,
    fun k => algebraMap _ (ex.nch.Oe w) ((uu : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) * algebraMap _ _ (o k)),
    cz * (c⁻¹ * ν), _, hN, ⟨m, hm1⟩, fun k => ⟨hh2, hy k⟩, ?_⟩
  intro yy hyy
  have eA : ∀ k, adForm (R2 p) j (yy k) (p.v₀ j (sg0 D p.P.A3.A)) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
      (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w))) ((R2 p).vP j ((R2 p).mu (D.plEq w)))
        (h * hQ * z0⁻¹) (y k) u) := fun k =>
    (congrArg (adForm (R2 p) j (yy k)) (funext hu)).symm.trans (hyy k u)
  have eE : ∀ k, e (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (algebraMap _ (ex.nch.Oe w)
      ((uu : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) * algebraMap _ _ (o k)))) =
      ((detChar (Vc D j) (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (h * hQ) : Circle) : ℂ) * (f k : ℂ) := fun k => by
    rw [h2, map_mul, hρ.ek_e, ho k, ← huu]
    rfl
  have eS : ∀ k, series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)))
      (h * hQ) (g k : PolF D (Wc D j).rank (Vc D j).rank) = (c⁻¹ * cz) •
      singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w))) ((R2 p).vP j ((R2 p).mu (D.plEq w)))
        (h * hQ * z0⁻¹) (y k) u := fun k => by
    have e1 : (g k : PolF D (Wc D j).rank (Vc D j).rank) = c⁻¹ • (R2 p).ioP j (PiTensorProduct.tprod ℂ u) (y k) := by
      rw [hyio k, smul_smul, inv_mul_cancel₀ c0, one_smul]
    rw [e1, map_smul, hB0.series_eq_ser, hfl]
    funext g'
    have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z0⁻¹ cz (inv_mem hzf) u (h * hQ) (y k) g'
    simp only [Pi.smul_apply, smul_eq_mul] at e3 ⊢
    rw [e3]
    simp only [GlobalTheory.ConjTwist.ser, singleSeries]
    ring
  rw [hgen, GlobalTheory.TwTraceCx.gen_eq_smul hB ht hadm (hρ.weil_base _ _ _) hω,
    ← s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, ← hsum, map_sum, map_sum]
  simp only [Subring.smul_def, map_smul, eS, eA, eE, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  field_simp

end Point

theorem twGen_cx : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → TwAdm → TwChr → AtFit fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ z ∈ twSet hρ (rdAt p w j hρ ν) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w),
  ∃ (n : ℕ) (h : Fin n → GA (Fm.D x i) (Vc (Fm.D x i) j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc (Fm.D x i) j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun _ _ _ _ hAdm hChr =>
  AtTw.imp (AtTw.and hAdm (AtTw.and hChr (AtTw.and GlobalTheory.T.LatticeSmallGeneration GlobalTheory.T.lattice_intersection_at_place))) fun Fm x hx i p hr hm w hw j ⟨a1, a2, a4, a5⟩ ρ hρ ν _ hfit _ e _ h2 z hz =>
    let ⟨c1, c2⟩ := a2 ρ hρ hfit.1
    cx_at GlobalTheory.T.places_bound_tuple GlobalTheory.T.flat_bound_tuple GlobalTheory.T.trace_bound_tuple twQ hr hm hw a1.1 hρ hfit (a4 ρ hρ hfit.1.1) a5 c1 c2 e h2 z hz

end GlobalTheory.BigOn.Exp.TwCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairs
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.Pair

theorem exists_ext {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    (hf : Function.Injective f) :
    ∃ j : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing V), Ext f j := by
  let g : R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) _).comp ((algebraMap V (FractionRing V)).comp f)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      ((IsFractionRing.injective V (FractionRing V)).comp hf)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) := (IsFractionRing.lift hg).toAlgebra
  refine ⟨(IsAlgClosed.lift : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R]
    AlgebraicClosure (FractionRing V)).toRingHom, fun r => ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap]
  rfl

theorem sq {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) (hj : Ext f j) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (hκ : κ ≫ jK R = jK V ≫ spMap f) :
    spMap j ≫ jFK (R := R) F₀ = jFK (R := V) F ≫ κ := by
  haveI : Mono (jK R) :=
    haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := CommRingCat.of (FractionRing R))
      (nonZeroDivisors R)
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  rw [← cancel_mono (jK R), Category.assoc, Category.assoc, hκ]
  simp only [jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

end GlobalTheory.TInj.Pair

theorem GlobalTheory.TInj.pull_pair_match : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → J.map f₁ ≤ maximalIdeal V → J.map f₂ ≤ maximalIdeal V → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ y₀ = κ₂ ≫ y₀ → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ p₀ : QkPt D₀.toPre (AlgebraicClosure (FractionRing R)) n, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) := by
  intro X g n B _ ζ sX c hζ hn R _ _ _ J hJ D₀ A₀ G₀ _ _ U₀ hG₀ y₀ α₀ hO V _ _ _ _ hV f₁ f₂ hf₁ hf₂ hJ₁ hJ₂
    κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, hD₁, A₁, U₁, hG₁, hU₁, tr₁⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₁ hf₁ hJ₁
  obtain ⟨D₂, hD₂, A₂, U₂, hG₂, hU₂, tr₂⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₂ hf₂ hJ₂
  obtain ⟨α₁, hO₁, hα₁⟩ := GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₁ D₁ hD₁ A₁ U₁ hU₁ y₀ α₀ hO κ₁ hκ₁
  obtain ⟨α₂, hO₂, hα₂⟩ := GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₂ D₂ hD₂ A₂ U₂ hU₂ y₀ α₀ hO κ₂ hκ₂
  rw [← hy] at hO₂
  obtain ⟨b, φ, hM, hQ⟩ := GlobalTheory.T.two_trait_uniformisations_matching_data c V hV D₁ A₁ _ U₁ D₂ A₂ _ U₂ hG₁ hG₂ (κ₁ ≫ y₀) α₁ α₂ hO₁ hO₂
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.TInj.Pair.exists_ext f₁ hf₁
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.TInj.Pair.exists_ext f₂ hf₂
  refine ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ, hj₁, hj₂, hM, fun p₀ => ?_⟩
  obtain ⟨x₀, hx₀, hpow⟩ := (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv R J hJ D₀ A₀ G₀ U₀ hG₀ (AlgebraicClosure (FractionRing R)) n hn).1 p₀
  obtain ⟨l, hl⟩ := GlobalTheory.T.torsionPoint_siegelFibre_eq_levelSection c hζ A₀.A y₀ α₀ hO.1 (AlgebraicClosure (FractionRing R))
    (jFK (R := R) (AlgebraicClosure (FractionRing R))) x₀ hpow
  obtain ⟨p₁, x₁, hy₁, hT₁, hq₁, hc₁⟩ := tr₁ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₁ hj₁ n hn p₀ x₀ hx₀
  obtain ⟨p₂, x₂, hy₂, hT₂, hq₂, hc₂⟩ := tr₂ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₂ hj₂ n hn p₀ x₀ hx₀
  have e₁ := hα₁ _ x₁.left (spMap j₁ ≫ x₀.left) (hc₁.trans (Category.assoc _ _ _).symm)
  have e₂ := hα₂ _ x₂.left (spMap j₂ ≫ x₀.left) (hc₂.trans (Category.assoc _ _ _).symm)
  have s₁ := GlobalTheory.TInj.Pair.sq f₁ j₁ hj₁ κ₁ hκ₁
  have s₂ := GlobalTheory.TInj.Pair.sq f₂ j₂ hj₂ κ₂ hκ₂
  have key : x₁.left ≫ α₁ = x₂.left ≫ α₂ := by
    rw [e₁, e₂, Category.assoc, Category.assoc, hl, ← Category.assoc, ← Category.assoc (spMap j₂), s₁, s₂,
      Category.assoc, Category.assoc, ← Category.assoc κ₁, ← Category.assoc κ₂, hy]
  exact ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ n hn p₁ p₂ x₁ x₂ hq₁ hq₂ key⟩
end
end

