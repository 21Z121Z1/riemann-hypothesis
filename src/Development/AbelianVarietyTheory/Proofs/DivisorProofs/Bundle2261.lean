import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  first | exact @GlobalTheory.MBLow.bKey_adapted_map | exact GlobalTheory.MBLow.bKey_adapted_map | (intros; apply GlobalTheory.MBLow.bKey_adapted_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsFiniteType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

theorem abelianScheme_descends_to_fg_subring_anyDim :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA, hφ⟩

end GlobalTheory.AbelianLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftArtinPinch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PinchUnitLift

theorem unit_lift (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (h : IsPullback f₁ f₂ g₁ g₂) [IsLocalRing P] (h₁ : Function.Surjective g₁) (h₂ : Function.Surjective g₂)
    (r : R₀) (hr : IsUnit r) : ∃ s : R₁, IsUnit s ∧ g₁ s = r := by
  rcases subsingleton_or_nontrivial R₀ with h0 | h0
  · exact ⟨1, isUnit_one, Subsingleton.elim _ _⟩
  have hf : Function.Surjective f₁ := by
    intro a
    obtain ⟨b, hb⟩ := h₂ (g₁ a)
    obtain ⟨p, hp, -⟩ := Types.exists_of_isPullback (h.map (forget CommRingCat)) a b hb.symm
    exact ⟨p, hp⟩
  haveI : Nontrivial R₁ := g₁.hom.domain_nontrivial
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf
  haveI : IsLocalHom g₁.hom := IsLocalHom.of_surjective g₁.hom h₁
  obtain ⟨s, rfl⟩ := h₁ r
  exact ⟨s, IsUnit.of_map g₁.hom s hr, rfl⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (B : Over (Spec R₀)) [GrpObj B], IsAbelianScheme B → ∀ (X₁ : Scheme.{0}) (q : X₁ ⟶ Spec R₁) (ρ : B.left ⟶ X₁), ρ ≫ q = B.hom ≫ Spec.map g₁ → ∀ u : Γ(B.left, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : B.left, gm ρ x ⊤ v = gm (𝟙 B.left) x ⊤ u := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ h₁ h₂ B _ hB X₁ q ρ hρ u
  have hb := GlobalTheory.globalFns_holds _ B hB
  obtain ⟨t, ht⟩ := hb.2 u.val
  obtain ⟨t', ht'⟩ := hb.2 (u⁻¹).val
  have htu : IsUnit t := by
    refine IsUnit.of_mul_eq_one t' (hb.1 ?_)
    rw [map_mul, map_one, ht, ht']
    exact u.mul_inv
  obtain ⟨s, hs, hst⟩ := unit_lift P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h h₁ h₂ ((Scheme.ΓSpecIso R₀).hom t)
    (htu.map (Scheme.ΓSpecIso R₀).hom.hom)
  have hv : IsUnit (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) := (hs.map _).map _
  refine ⟨hv.unit, fun x => Units.ext ?_⟩
  rw [gm_val ρ x ⊤ trivial, gm_val (𝟙 B.left) x ⊤ trivial]
  have e : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) = u.val := by
    have e1 : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) =
        (ρ ≫ q).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have e2 : (Spec.map g₁).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) = t := by
      have := congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_inv_naturality g₁)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [← this]
      have hst' : g₁.hom s = (Scheme.ΓSpecIso R₀).hom.hom t := hst
      rw [hst']
      exact (Scheme.ΓSpecIso R₀).hom_inv_id_apply t
    rw [e1, hρ, Scheme.Hom.comp_appTop, ← ht, ← e2]
    rfl
  exact congrArg (B.left.presheaf.germ ⊤ x trivial).hom e

end GlobalTheory.PinchUnitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricFinitelyManyPlaces
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem Cover.exists_valuationRing_point {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)
    {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (hz : z ≫ V.π = y.1) :
    ∃ yt : Sp e.O ⟶ V.X, spMap e.O.subtype ≫ yt = z ≫ V.j ∧
      ∀ U : V.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U → ⊤ ≤ yt ⁻¹ᵁ U := by
  have hP : IsProper V.p := by
    obtain ⟨N, j, hj, he⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← he]; infer_instance
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O :=
    ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨l.l, l.fac_left, fun U hU => ((IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU).ge⟩

theorem Cover.finite_places_lg_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), k ≠ 0 → V.Induces A L k → ∀ y : AlgPt Y, {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, A.lg v e y ≠ 0}.Finite := by
  intro F _ _ C Y V A L k hk0 hI y
  obtain ⟨r, -, -, -, hfin⟩ := hI
  obtain ⟨z, hz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1
  have := V.ar.isNoetherian
  have hcov : (Set.univ : Set V.X) ⊆ ⋃ i, (L.B.U i : Set V.X) := by
    intro x _
    have hx : x ∈ (⨆ i, L.B.U i : V.X.Opens) := by rw [L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.B.U i : Set V.X))
    (fun i => (L.B.U i).isOpen) hcov
  let a : L.B.ι → AlgebraicClosure F := fun i =>
    valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r (fun _ => i) : V.G.functionField))
  have hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | a i ≠ 0 ∧ ∃ e : TrueGeo.Ext v, e.w (a i) ≠ 1}.Finite := by
    intro i
    by_cases h : a i = 0
    · simp [h]
    · exact (GlobalTheory.TrueGeo.finite_ext_ne_one F (a i) h).subset fun v hv => hv.2
  refine (S.finite_toSet.biUnion fun i _ => hB i).subset ?_
  rintro v ⟨e, he⟩
  obtain ⟨yt, hyt, hU⟩ := V.exists_valuationRing_point e y z hz
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h := hfin v e y z yt (fun _ => i) hz hyt (hU _ hi)
  by_contra h2
  have hlog : Real.log (e.w (a i)) = 0 := by
    by_cases h0 : a i = 0
    · simp [h0]
    · have : e.w (a i) = 1 := by
        by_contra hne
        exact h2 (Set.mem_iUnion₂.mpr ⟨i, hiS, h0, e, hne⟩)
      simp [this]
  have h3 : (k : ℝ) * A.lg v e y = 0 := h.trans hlog
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  exact he ((mul_eq_zero.mp h3).resolve_left hk)

end GlobalTheory.Mean4O
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def stalkAlg (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) : c.F →+* (X₀ TF.Y Z).presheaf.stalk x :=
  ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom.comp (algX (s₀ TF.Y Z) ⊤)

def stalkHom (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).presheaf.stalk x :=
  ((X₀ TF.Y Z).presheaf.germ ((barComp TF.Y Z).ι ⁻¹ᵁ U.1) x hx).hom.comp ((barComp TF.Y Z).ι.app U.1).hom

theorem algebraMap_comp_stalkAlg (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) :
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (stalkAlg TF Z x) =
      GlobalTheory.Cartier.constFn (s₀ TF.Y Z) :=
  RingHom.ext fun a => GlobalTheory.Cartier.algebraMap_germ (U := ⊤) trivial _

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCubeProductValueFderivAtZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero : ∀ {g : ℕ} (x y W : Fin g → ℂ) (fr : thK.{0} → (Fin g → ℂ) → ℂ) (F : (Fin g → ℂ) → ℂ),
    F =ᶠ[nhds 0] (fun z => ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    (∀ I : thK.{0}, DifferentiableAt ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)) →
    (∀ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0) →
    (∀ I : thK.{0}, 2 ∉ I.down → fr (ULift.up (insert 2 I.down)) = fr I) →
    F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (ULift.up {0, 1, 2})) (x + y) W / fr (ULift.up {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (ULift.up {2})) 0 W / fr (ULift.up {2}) 0 -
        fderiv ℂ (fr (ULift.up {0, 2})) x W / fr (ULift.up {0, 2}) x -
        fderiv ℂ (fr (ULift.up {1, 2})) y W / fr (ULift.up {1, 2}) y := by
  first | exact @GlobalTheory.AltJet.value_and_fderiv_at_zero | exact GlobalTheory.AltJet.value_and_fderiv_at_zero | (intros; apply GlobalTheory.AltJet.value_and_fderiv_at_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcPropertyLocalisationBaseChangeOfModelStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcProperty_localisationBaseChange_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 := by
  first | exact @GlobalTheory.LocArc.arc_localise | exact GlobalTheory.LocArc.arc_localise | (intros; apply GlobalTheory.LocArc.arc_localise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariantStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_forms_span_invariant : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  first | exact @GlobalTheory.IntFormsRank.rkK_Mall | exact GlobalTheory.IntFormsRank.rkK_Mall | (intros; apply GlobalTheory.IntFormsRank.rkK_Mall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactor
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvSmall

theorem fullRk_irred : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), GlobalTheory.FullRankCoinv.augRk n d ν ≤ N →
      N ≤ GlobalTheory.FullRankCoinv.fullRk k n d → (∀ h : GL (Fin d) k, ∀ Ψ ∈ N, (fun Y => Ψ (Y * h.1)) ∈ N) →
      N = GlobalTheory.FullRankCoinv.augRk n d ν ∨ N = GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := GlobalTheory.T.full_rank_coinvariant_induced_iso k n d ν hnd hs
  rcases GlobalTheory.T.induced_full_rank_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by
    rintro _ ⟨Ψ, hΨ, rfl⟩ h₀; exact ⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE
  · left
    refine le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA
    have : Z Ψ ∈ N.map Z := ⟨Ψ, hΨ, rfl⟩
    rw [hE] at this
    exact (Submodule.mem_bot ℂ).1 this
  · right
    refine le_antisymm hNF (fun Ψ hΨ => ?_)
    have : Z Ψ ∈ N.map Z := hE ▸ hZ1 Ψ hΨ
    obtain ⟨Ψ', hΨ', he⟩ := this
    have h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν :=
      hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])
    have := N.add_mem hΨ' (hA h1)
    rwa [add_sub_cancel] at this

theorem irr_small : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν N hAN hNS hN
  obtain ⟨t, ι, ν₀, hs, hu, hbij, hso, hg, hh⟩ := GlobalTheory.T.exists_unramified_linear_bar_dual hP F E σ B a a' G X om om' hT v hv
  have hR := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv hν t
  have haugSB : augAt om' v ≤ SB _ := Submodule.span_le.2 (by
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ)

  have hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤
      (augAt om' v).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ.1
    obtain ⟨g, hgU, hg'⟩ := hg g₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hg' φ hφ
    refine ⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩
    · rw [← he]
      exact Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1
    · intro Y hY
      rw [← he]
      show ι φ₁ Y - ι φ Y = 0
      rw [he, hΨ.2 Y hY]
      simp only [GlobalTheory.FullRankCoinv.lact, sub_zero]
      rw [hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
        rw [Matrix.det_transpose]; exact (Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]
  set N' := N.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') with hN'
  have hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N' :=
    hgen.trans (inf_le_inf_right _ (Submodule.map_mono hAN))
  have hst : ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N' := by
    rintro h₀ _ ⟨⟨φ, hφN, rfl⟩, hΨ⟩
    obtain ⟨h, hhU, c, hc, hh'⟩ := hh h₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hh' φ (hNS hφN)
    have h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁ := by
      rw [he]; funext Y; simp [hc]
    refine ⟨⟨c⁻¹ • φ₁, N.smul_mem _ (hN h hhU φ hφN φ₁ hφ₁ hA), by rw [map_smul, h1]⟩, ?_, ?_⟩
    · rw [h1]; exact Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)
    · intro Y hY
      exact hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])
  have hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι φ = ι φ' → φ = φ' := fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e
  have hloc : ∀ φ₀ ∈ G.M'.SoLoc B.ψ t, ι φ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') :=
    fun φ₀ h0 => ⟨hbij.mapsTo h0.1, (hso φ₀ h0.1).1 h0⟩
  rcases fullRk_irred hP (Fv F v) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE
  · left
    refine le_antisymm (fun φ hφN => ?_) hAN
    obtain ⟨φ₀, h0, hd⟩ := hR φ (hNS hφN)
    have h0N : φ₀ ∈ N := by
      have := N.sub_mem hφN (hAN hd); rwa [sub_sub_cancel] at this
    have h1 : ι φ₀ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ := hE ▸ ⟨⟨φ₀, h0N, rfl⟩, hloc φ₀ h0⟩
    obtain ⟨⟨w, hw, hwe⟩, -⟩ := hgen h1
    have : w = φ₀ := hinj w (haugSB hw) φ₀ h0.1 hwe
    subst this
    have := (augAt om' v).add_mem hw hd
    rwa [add_sub_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφ => ?_)
    obtain ⟨φ₀, h0, hd⟩ := hR φ hφ
    have h1 : ι φ₀ ∈ N' := hE ▸ hloc φ₀ h0
    obtain ⟨⟨φ', hφ'N, he⟩, -⟩ := h1
    have : φ' = φ₀ := hinj φ' (hNS hφ'N) φ₀ h0.1 he
    subst this
    have := N.add_mem hφ'N (hAN hd)
    rwa [add_sub_cancel] at this

end GlobalTheory.IrrCoinvSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCompleteConnectedStatement
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_complete_connected : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), Function.Injective φ → IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens), IsIntegral X → Flat s → GeomIrr s Xw → ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  first | exact @GlobalTheory.FlatModel.connected_pullback_of_geomIrr | exact GlobalTheory.FlatModel.connected_pullback_of_geomIrr | (intros; apply GlobalTheory.FlatModel.connected_pullback_of_geomIrr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem appLE_comp_cst {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (U : W.Opens) (A : W'.Opens) (h : A ≤ π ⁻¹ᵁ U) :
    (π.appLE U A h).hom.comp (cst f U) = cst (π ≫ f) A := by
  have e : f.appTop ≫ W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ π.appLE U A h =
      (π ≫ f).appTop ≫ W'.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop]
    simp [Scheme.Hom.appLE]
  ext r
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem cst_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (U : W.Opens) :
    cst (p ≫ Spec.map (CommRingCat.ofHom φ)) U = (cst p U).comp φ := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem comap_baseIdeal {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (J : Ideal R) : (baseIdeal f J).comap π = baseIdeal (π ≫ f) J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {p : W.affineOpens × W'.affineOpens // p.2.1 ≤ π ⁻¹ᵁ p.1.1}) (fun i => i.1.2) ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ (π x)))
    obtain ⟨A, hA, hxA, hAU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 W'.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U.1 from hxU)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(U, ⟨A, hA⟩), hAU⟩, hxA⟩
  · intro i
    rw [GlobalTheory.Principalise.comapIdealAffine _ π i.1.1 i.1.2 i.2, baseIdeal_ideal, baseIdeal_ideal, Ideal.map_map,
      appLE_comp_cst]

theorem baseIdeal_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R) :
    baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ) := by
  rw [baseIdeal, baseIdeal, Ideal.map_map, cst_comp_specMap]

theorem mem_support_baseIdeal {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (J : Ideal R) (x : W) : x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal := by
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
  have key : ∀ r, x ∈ W.basicOpen (cst f U.1 r) ↔ r ∉ (f x).asIdeal := by
    intro r
    simp only [cst, rs, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    simp only [hxU, TopologicalSpace.Opens.mem_inf, true_and]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, baseIdeal_ideal]
  unfold Ideal.map
  rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h r hr
    by_contra hn
    exact h _ ⟨r, hr, rfl⟩ ((key r).2 hn)
  · rintro h _ ⟨r, hr, rfl⟩ hx
    exact (key r).1 hx (h hr)

theorem baseIdeal_calculus :
    (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) :=
  ⟨fun _ _ _ _ f π J => comap_baseIdeal f π J,
    fun _ _ _ _ φ _ p J => baseIdeal_comp_specMap φ p J,
    fun _ _ _ f J x => mem_support_baseIdeal f J x⟩

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bound_statement_holds : BoundSt := by
  first | exact @GlobalTheory.FlatModel.boundSt | exact GlobalTheory.FlatModel.boundSt | (intros; apply GlobalTheory.FlatModel.boundSt <;> assumption)
end

