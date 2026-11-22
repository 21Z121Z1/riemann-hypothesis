import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3649
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3580
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowup
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin

namespace GlobalTheory.AllChart

theorem preChart_all : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, PreChart F (π ≫ z) j φ BD d x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow x
  obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, hx⟩ :=
    GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
  have : IsCommMonObj G₁ := hfam.1.comm
  obtain ⟨het, hsep⟩ :=
    GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap GlobalTheory.T.chartSeparation_data_defined_over_centre_field g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
  have h := GlobalTheory.T.preChart_of_tautologicalChart_etaleCompletion g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy het hsep
  rwa [hx] at h

end GlobalTheory.AllChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem uPre_of_boundary_pointRigid {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x := by
  obtain ⟨k, _, m, e, C, ξ, hT, hy, hξ⟩ :=
    GlobalTheory.T.exists_pointRigid_tautological_chart_unitary_boundary Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx
  have hE := GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨hset, hred, a, ha, hbd⟩ :=
    GlobalTheory.T.tautologicalChart_boundary_equations Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  exact ⟨k, inferInstance, m, e, C, ξ, a, hT.1, hy, hξ, hE, hred, hset, ha, hbd⟩

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerIsoSmoothSncToroidalModelStatement
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
theorem _root_.GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  first | exact @GlobalTheory.LogKSAssembly.hasLogKS | exact GlobalTheory.LogKSAssembly.hasLogKS | (intros; apply GlobalTheory.LogKSAssembly.hasLogKS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem RepFam.smoothOfRelativeDimension : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  intro p _ D R _ _ b N hN hNp F hq
  have hlft : LocallyOfFiniteType F.s := by
    obtain ⟨M, i, hi, hqc, hi'⟩ := hq
    have := isProper_str R M
    rw [← hi']
    infer_instance
  have hsm : Smooth F.s := by
    refine GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base R F.X F.s hlft ?_
    intro C C₀ _ _ _ _ π hπ hker t x₀ hx
    obtain ⟨β, rfl⟩ : ∃ β : R →+* C, t = spMap β :=
      ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    have hcomp : spMap π ≫ spMap β = spMap (π.comp β) := by
      simp [spMap, ← Spec.map_comp]
    have hs₀ : x₀ ≫ F.s = spMap (π.comp β) := by rw [hx, hcomp]
    obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObjectPullback p D R b N _ _ F.s _ F.univ x₀ hs₀
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift p D R b N hN hNp C C₀ π β hπ (by rw [← hker, pow_two]) o₀
    obtain ⟨x, ⟨hxs, ⟨mx⟩⟩, -⟩ := F.rep (Sp C) (spMap β) o'
    obtain ⟨mc⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ o₀ o' F.univ (spMap π) x m' mx
    refine ⟨x, ?_, hxs⟩
    exact (F.rep (Sp C₀) (spMap (π.comp β)) o₀).unique
      ⟨by rw [Category.assoc, hxs, hcomp], ⟨mc⟩⟩ ⟨hs₀, ⟨m₀⟩⟩
  exact GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent R F.X F.s _ hsm (GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily p D R b N hN hNp F hq hsm)

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowup
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped TensorProduct

namespace GlobalTheory.BlowSmooth

theorem formallySmooth_of_regular_fibre {A B : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsLocalRing B] (σ : A →+* B) [IsLocalHom σ] [PerfectField (ResidueField A)] (hf : σ.Flat) (he : σ.EssFiniteType)
    (hr : IsRegularLocalRing (B ⧸ (maximalIdeal A).map σ)) : σ.FormallySmooth := by
  algebraize [σ]
  have : IsLocalHom (algebraMap A B) := ‹_›
  let e : (B ⧸ (maximalIdeal A).map σ) ≃+* ResidueField A ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ maximalIdeal A)).toRingEquiv
  have : IsRegularLocalRing (ResidueField A ⊗[A] B) := .of_ringEquiv e
  have : Algebra.FormallySmooth (ResidueField A) (ResidueField A ⊗[A] B) :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _
  have : Algebra.FinitePresentation A (Algebra.EssFiniteType.subalgebra A B) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := A) (S := B)
    (Algebra.EssFiniteType.submonoid A B)

theorem isRegularLocalRing_quotient_of_flat {B R : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
    [IsLocalRing R] (φ : B →+* R) (hf : φ.Flat) (hm : (maximalIdeal B).map φ = maximalIdeal R) (I : Ideal B) (hI : I ≠ ⊤)
    (hr : IsRegularLocalRing (R ⧸ I.map φ)) : IsRegularLocalRing (B ⧸ I) := by
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let χ : (B ⧸ I) →+* (R ⧸ I.map φ) := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map
  have hcomm : (Ideal.Quotient.mk (I.map φ)).comp φ = χ.comp (Ideal.Quotient.mk I) := by
    ext a; simp [χ]
  refine (GlobalTheory.RegSmooth.isRegularLocalRing_of_flat_of_map_maximalIdeal' χ (GlobalTheory.Pat.flat_quotientMap_map φ hf I) ?_).1
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map φ)) Ideal.Quotient.mk_surjective, ← hm,
    ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
    Ideal.map_map, hcomm]

theorem perfectField_residueField {o : Type} [CommRing o] [IsDedekindDomain o] [CharZero o] [Algebra.FiniteType ℤ o]
    (q : Ideal o) [q.IsPrime] : PerfectField q.ResidueField := by
  obtain ⟨p, hp⟩ := CharP.exists q.ResidueField
  rcases CharP.char_is_prime_or_zero q.ResidueField p with h | rfl
  · have : Fact p.Prime := ⟨h⟩
    have hq : q ≠ ⊥ := by
      rintro rfl
      have h1 : algebraMap o (⊥ : Ideal o).ResidueField (p : o) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero _ p
      rw [Ideal.algebraMap_residueField_eq_zero, Ideal.mem_bot] at h1
      exact h.ne_zero (Nat.cast_eq_zero.1 h1)
    have : q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq
    have : Algebra.FiniteType ℤ q.ResidueField :=
      Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom ℤ o q.ResidueField)
        (Ideal.algebraMap_residueField_surjective q)
    let _ : Algebra (ZMod p) q.ResidueField := ZMod.algebra _ p
    have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := q.ResidueField) (RingHom.ext_int _ _)
    have : Algebra.FiniteType (ZMod p) q.ResidueField := .of_restrictScalars_finiteType ℤ _ _
    have : Module.Finite (ZMod p) q.ResidueField := finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.perfectField (ZMod p)
  · have : CharZero q.ResidueField := CharP.charP_to_charZero _
    infer_instance

set_option backward.isDefEq.respectTransparency false in

theorem formallySmooth_stalkMap {o : Type} [CommRing o] [IsDedekindDomain o] {S : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (hp : ∀ (q : Ideal o) [q.IsPrime], PerfectField q.ResidueField) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hξ : ξ ≫ s = spMap b) (hb : Function.Injective b)
    (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (hr : IsRegularLocalRing (R ⧸ ((maximalIdeal R).comap b).map b)) :
    (s.stalkMap (ξ (closedPoint R))).hom.FormallySmooth := by
  set y := ξ (closedPoint R) with hy
  let φ₀ : S.presheaf.stalk y →+* R := (Scheme.stalkClosedPointTo ξ).hom
  let σ := (s.stalkMap y).hom
  let L := Localization.AtPrime (s y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of o) (s y)
  let τ : L →+* S.presheaf.stalk y := σ.comp e.inv.hom
  let ρ : o →+* S.presheaf.stalk y := τ.comp (algebraMap o L)
  have h3 : (Sp o).fromSpecStalk (s y) = Spec.map e.inv ≫ spMap (algebraMap o L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (s y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := s y)).symm
  have hb' : b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk s (x := y)
    have key : spMap b = spMap (φ₀.comp ρ) := by
      rw [← hξ, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, τ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (s y).asIdeal = (maximalIdeal R).comap b := by
    have : s y = spMap b (closedPoint R) := by
      rw [hy, ← hξ, Scheme.Hom.comp_apply]
    rw [this]; rfl
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  have hφ : Function.Injective φ₀ := by
    have h1 : φ₀.Flat := het.1
    algebraize [φ₀]
    have : IsLocalHom (algebraMap (S.presheaf.stalk y) R) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo ξ).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := S.presheaf.stalk y) (B := R)
    exact FaithfulSMul.algebraMap_injective (S.presheaf.stalk y) R
  have : IsDomain (S.presheaf.stalk y) := hφ.isDomain φ₀
  have hρ : Function.Injective ρ := by
    rw [hb'] at hb
    exact Function.Injective.of_comp (f := φ₀) hb
  have hτ : τ.Flat := by
    algebraize [τ, ρ]
    have : FaithfulSMul o (S.presheaf.stalk y) := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ
    have : IsScalarTower o L (S.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
    exact (Module.flat_iff_of_isLocalization L (s y).asIdeal.primeCompl (S.presheaf.stalk y)).2 inferInstance
  have hess : τ.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.FiniteType.of_surjective _ e.commRingCatIsoToRingEquiv.symm.surjective).essFiniteType
      (LocallyOfFiniteType.stalkMap s y)
  have : IsLocalHom e.inv.hom := isLocalHom_of_isIso e.inv
  have : IsLocalHom τ := RingHom.isLocalHom_comp _ _
  have : PerfectField (ResidueField L) := hp (s y).asIdeal
  have hI : ((maximalIdeal L).map τ).map φ₀ = ((maximalIdeal R).comap b).map b := by
    rw [← hq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hb']
  have hne : (maximalIdeal L).map τ ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap τ).ge)
  have hreg := isRegularLocalRing_quotient_of_flat φ₀ het.1 het.2.1 _ hne (hI ▸ hr)
  have hs := formallySmooth_of_regular_fibre τ hτ hess hreg
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso e.inv (s.stalkMap y)).1 hs

theorem smoothOfRelativeDimension_of_dense {U X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (n : ℕ) (hn : SmoothOfRelativeDimension n (j ≫ f)) : SmoothOfRelativeDimension n f := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose r W hW hr using H1.exists_dim f
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  obtain ⟨_, hu, u, rfl⟩ := hj.inter_open_nonempty _ (W x).2 ⟨x, hW x⟩
  have h₁ : SmoothOfRelativeDimension (0 + r x) ((j ∣_ W x) ≫ (W x).ι ≫ f) := have := hr x; inferInstance
  have h₂ : SmoothOfRelativeDimension (0 + n) ((j ⁻¹ᵁ W x).ι ≫ j ≫ f) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
  have e := H1.dim_unique _ h₁ h₂ ⟨u, hu⟩
  rw [zero_add, zero_add] at e
  exact e ▸ hr x

theorem smoothOfRelativeDimension_blowup : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow
  have hiz : i ≫ z = F.s := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, h, -⟩, -⟩ := hmin
    exact h
  obtain ⟨hproj, hdense, hji⟩ : IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i := by
    obtain ⟨_, -, -, -, -, h₁, h₂, h₃, -⟩ := hblow
    exact ⟨h₁, h₂, h₃⟩
  have hjs : j ≫ π ≫ z = F.s := by rw [← Category.assoc, hji, hiz]
  have : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have : IsProper (π ≫ z) := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  have : LocallyOfFinitePresentation (π ≫ z) := inferInstance
  have : Smooth (π ≫ z) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
    rintro x -
    obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, rfl⟩ :=
      GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
    have : IsCommMonObj G₁ := hfam.1.comm
    obtain ⟨het, -⟩ :=
      GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap GlobalTheory.T.chartSeparation_data_defined_over_centre_field g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
    obtain ⟨-, -, hinj, -, -, hreg⟩ := TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
    have hξ : ξ ≫ π ≫ z = spMap C.b := by
      have h1 : jK C.R ≫ ξ ≫ π ≫ z = jK C.R ≫ spMap C.b := by
        rw [← Category.assoc, ← hy, Category.assoc, hjs, hfam.2.2.2.2]
      obtain ⟨c, hc⟩ := Spec.map_surjective (ξ ≫ π ≫ z)
      rw [← hc, jK, spMap, ← Spec.map_comp, ← Spec.map_comp] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      rw [← hc, spMap]
      congr 1
      ext a
      exact IsFractionRing.injective C.R (FractionRing C.R) (congr($h2 a))
    exact formallySmooth_stalkMap (π ≫ z) (fun q _ => perfectField_residueField q) C.b ξ hξ hinj het hreg
  exact smoothOfRelativeDimension_of_dense (π ≫ z) j hdense _ (hjs ▸ F.smooth)

end GlobalTheory.BlowSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBaseStatement
section
open GlobalTheory.UChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  first | exact @GlobalTheory.UPoincTop.uStB | exact GlobalTheory.UPoincTop.uStB | (intros; apply GlobalTheory.UPoincTop.uStB <;> assumption)
end

