import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerValMulWedgeCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomologicalCsdTemperedUnrOfFull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalPrimeDivisorIntegralEqGenericFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mix.cycInt_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  intro k K _ _ _ _ X G _ p q j hp τ e hX L f x hx
  obtain ⟨hGi, hGn, hGproj, hGdim, hgen, hinj, hstalk, hcoh, hempty⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K X G p q j hp (e + 1) hX
  obtain ⟨hZi, hZgen, hZdim, hZuniv⟩ := GlobalTheory.ClosFacts.clos_facts X (j x)
  obtain ⟨hxi, hxgen, -, hxuniv⟩ := GlobalTheory.ClosFacts.clos_facts G x

  have hK : CharZero K := by
    have := hX.charZero_base
    exact (RingHom.charZero_iff (IsFractionRing.injective k K)).1 inferInstance
  have hc : CharZero Γ(clos (j x), ⊤) := by
    obtain ⟨g0, hg0, -, -, -⟩ := hZuniv (clos x) (closι x ≫ j) (by
      simp only [Scheme.Hom.comp_apply, hxgen])
    have : IsDomain Γ(clos x, ⊤) := inferInstance
    let φ : K →+* Γ(clos x, ⊤) :=
      ((closι x ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have : CharZero Γ(clos x, ⊤) := (RingHom.charZero_iff φ.injective).1 hK
    exact g0.appTop.hom.charZero
  have hdim : topologicalKrullDim (clos (j x)) = (e + 1 : ℕ) := by
    rw [hZdim]
    have h1 := (GlobalTheory.MixHt.dimOne k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) (e + 1) hX.dim_eq).1 (j x)
    exact h1.1 ((hcoh x).trans hx)
  have hZ : IsArithVar (closι (j x) ≫ p) e := hX.of_isClosedImmersion (closι (j x)) hc hdim
  haveI := hZi
  let G' := Limits.pullback (closι (j x) ≫ p) (spMap (algebraMap k K))
  let j' : G' ⟶ clos (j x) := Limits.pullback.fst _ _
  let q' : G' ⟶ Sp K := Limits.pullback.snd _ _
  have hp' : IsPullback j' q' (closι (j x) ≫ p) (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hG'i, -, hG'proj, -, hG'gen, -, -, -, -⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K (clos (j x)) G' (closι (j x) ≫ p) q' j' hp' e hZ
  have hw : (j' ≫ closι (j x)) ≫ p = q' ≫ spMap (algebraMap k K) := by
    rw [Category.assoc]; exact hp'.w
  let g : G' ⟶ G := hp.lift (j' ≫ closι (j x)) q' hw
  have hg1 : g ≫ j = j' ≫ closι (j x) := hp.lift_fst _ _ hw
  have hg2 : g ≫ q = q' := hp.lift_snd _ _ hw
  have hp'' : IsPullback j' (g ≫ q) (closι (j x) ≫ p) (spMap (algebraMap k K)) := by rw [hg2]; exact hp'
  have hsq : IsPullback g j' j (closι (j x)) := IsPullback.of_right hp''.flip hg1 hp.flip
  have : IsClosedImmersion g := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  have hgx : g (genericPoint G') = x := by
    apply hinj
    rw [← Scheme.Hom.comp_apply, hg1, Scheme.Hom.comp_apply, hG'gen, hZgen]
  have hproj'' : IsProjOver (g ≫ q) := by rw [hg2]; exact hG'proj
  obtain ⟨-, h1⟩ := GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme K G G' q (g ≫ q) τ hGproj g rfl e (fun i => (L i).bc hp.w τ)
    (fun y => f (bcPt hp.w τ y))
  obtain ⟨-, h2⟩ := GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K (clos (j x)) G' (closι (j x) ≫ p) (g ≫ q) j' hp'' τ e hZ
    (fun i => (L i).pull (closι (j x)) rfl)
  have h3 := fun i => GlobalTheory.Mix.BcPull.bc_pull_isom k K (algebraMap k K) X G (clos (j x)) G' p q j hp.w (closι (j x)) j' g hg1
    hp''.w τ (L i)
  have h4 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver K G' (g ≫ q) τ hproj'' e _ _ h3
  conv_lhs => rw [← hgx]
  rw [h1]
  have h5 := (h2 (fun y => f (ptMap (closι (j x)) rfl _ y))).2
  change _ = Mix.int _ _
  rw [← h5]
  unfold Mix.int
  rw [h4 1, h4 (-1)]
  congr 2 <;> (funext y; exact congrArg f (Subtype.ext (by
    simp only [bcPt_val, PtsOver.map_val, ptMap, Category.assoc, hg1])))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vacV_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_left_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

theorem vac_fixed_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk k' hk' r hr
  have h1 := vacV_fixed F E σ B a a' G X om om' hT v w hin hvT k hk
  have h2 := GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hin hvT k' hk'
  have e : om (k, k') = om (k, 1) * om (1, k') := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr]

end GlobalTheory.InertSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_point_stalk : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  first | exact @GlobalTheory.KeyValZero.key_val_zero | exact GlobalTheory.KeyValZero.key_val_zero | (intros; apply GlobalTheory.KeyValZero.key_val_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul) | (exact GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.ClosedLev

theorem exists_nhd (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
    (p : Z ⟶ Spec (CommRingCat.of R)) (hφ : IsProper φ)
    (hc : IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ)) (z : Z)
    (hz : I ≤ (p z).asIdeal) : ∃ U : Z.Opens, z ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
  have hfin : (⇑φ ⁻¹' {z}).Finite := (GlobalTheory.T.fibre_subsingleton_of_closedImmersion_mod_ideal R I X Z φ p hc z hz).finite
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ z hfin
  obtain ⟨V, hV, hzV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hzV₀
  have hVf : IsFinite (φ ∣_ V) := GlobalTheory.PushFinite.isFinite_restrict_of_le φ hle
  obtain ⟨haff, hfr⟩ := GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite X Z φ V hV hVf
  obtain ⟨r, hr1, hr⟩ := GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod _ _ (φ.app V).hom hfr _ (GlobalTheory.T.surjective_sections_mod_baseIdeal_of_closedImmersion R I X Z φ p hc V hV haff)
  exact ⟨Z.basicOpen r, GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf R I Z p V hV r z hzV hz hr1, GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range X Z φ V hV haff r hr⟩

theorem isClosedImmersion_of_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  intro R _ I hI X Z φ p hφ hp hc
  let O : Z.Opens := ⨆ U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)}, U.1
  have hO : O = ⊤ := by
    have h0 := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI Z p hp ((O : Set Z)ᶜ) O.isOpen.isClosed_compl fun z hz hIz => by
      obtain ⟨U, hzU, hU⟩ := exists_nhd R I X Z φ p hφ hc z hIz
      exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩)
    exact TopologicalSpace.Opens.ext (by simpa [Set.compl_empty_iff] using h0)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)} => U.1) hO fun U => U.2

end GlobalTheory.ClosedLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlatOfConstMulPeriodDeterminant
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FlatMul

theorem eq_zero_of_real_smul_mem {g : ℕ} (S : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology S] {z : Fin g → ℂ}
    (h : ∀ t : ℝ, t • z ∈ S) : z = 0 := by
  by_contra h0
  have hc : Countable S := countable_of_Lindelof_of_discrete
  have : Countable ℝ := Function.Injective.countable (f := fun t : ℝ => (⟨t • z, h t⟩ : S))
    fun s t e => smul_left_injective ℝ h0 (congrArg Subtype.val e)
  exact not_countable this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {z w : Fin g → ℂ}
    (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact (u.ker _).1 (right_eq_mul.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

def Marked {s : Sp ℂ ⟶ Sp (KA l)} (o : Obj D l (baseKA l) s) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (Di : Datum H)
    (t : D.La →ₗ[𝓞 E] Di.La) (P : Di.La →+ (Fin g → ℂ)) : Prop :=
  Function.Injective P ∧ (∀ z, z ∈ u.Λ ↔ z ∈ P.range) ∧
    (∀ a : 𝓞 E, ∃ T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, u.ex (T z) = u.ex z ≫ o.t.act.act a) ∧
      ∀ v, P (a • v) = T (P v)) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), u.ex ((l.M : ℝ)⁻¹ • P (t a)) = o.eta a

theorem exists_lev {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'} {Hm : Matrix (Fin g) (Fin g) ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (hφ : IsTransport o o' u u' Hm Hm' φ)
    {Di : Datum H} {t : D.La →ₗ[𝓞 E] Di.La} (ht : ∀ b, ∃ a e, b = t a + l.M' • e)
    {P : Di.La →+ (Fin g → ℂ)} {P' : Di.La →+ (Fin g' → ℂ)} (hP : Marked o u Di t P) (hP' : Marked o' u' Di t P') :
    ∃ gm : Di.La ≃ₗ[𝓞 E] Di.La, IsLev l Di gm ∧ ∀ a, φ (P a) = P' (gm a) := by
  obtain ⟨i1, r1, a1, e1⟩ := hP
  obtain ⟨i2, r2, a2, e2⟩ := hP'
  obtain ⟨hΛ, hact, -, heta, -⟩ := hφ
  choose f hf using fun a => (r2 _).1 ((hΛ (P a)).2 ((r1 _).2 ⟨a, rfl⟩))
  have hsm : ∀ (a : 𝓞 E) v, f (a • v) = a • f v := fun a v => by
    obtain ⟨T, hT, hTP⟩ := a1 a
    obtain ⟨T', hT', hTP'⟩ := a2 a
    have := u'.discrete
    refine i2 ?_
    rw [hf, hTP, hTP', hf, ← sub_eq_zero]
    refine eq_zero_of_real_smul_mem u'.Λ fun r => ?_
    rw [smul_sub, ← map_smul φ, ← map_smul T, ← map_smul T', ← map_smul φ]
    exact sub_mem_of_ex_eq u' ((hact a _ _ (hT _)).trans (hT' _).symm)
  let F : Di.La →ₗ[𝓞 E] Di.La := ⟨⟨f, fun a b => i2 (by rw [map_add, hf, hf, hf, map_add, map_add])⟩, hsm⟩
  have hb : Function.Bijective F := by
    refine ⟨fun a b h => i1 (φ.injective ?_), fun b => ?_⟩
    · rw [← hf, ← hf]; exact congrArg P' h
    · obtain ⟨a, ha⟩ := (r1 _).1 ((hΛ (φ.symm (P' b))).1 (by rw [φ.apply_symm_apply]; exact (r2 _).2 ⟨b, rfl⟩))
      exact ⟨a, i2 ((hf a).trans (by rw [ha, φ.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective F hb, fun a ha => ?_, fun a => (hf a).symm⟩
  have hM : (l.M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  show ∃ e, F a = a + l.M • e
  refine Submodule.smul_induction_on ha (fun r hr b _ => ?_) ?_
  · obtain ⟨a₀, e₀, rfl⟩ := ht b
    have hm := Submodule.smul_mem_smul hr (Submodule.mem_top (R := 𝓞 E) (x := a₀))
    obtain ⟨e, he⟩ := (r2 _).1 (sub_mem_of_ex_eq u' ((heta _ _ (e1 _ hm)).trans (e2 _ hm).symm))
    have h1 : F (t (r • a₀)) = t (r • a₀) + l.M • e := i2 (by
      rw [map_add, map_nsmul, he, map_smul φ, ← hf, ← smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀ hM,
        add_sub_cancel]
      rfl)
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e + k • (F (r • e₀) - r • e₀), ?_⟩
    rw [smul_add, ← map_smul t, smul_comm r l.M', map_add, h1, map_nsmul, hk, mul_smul, mul_smul, smul_add, smul_sub,
      smul_sub]
    abel
  · rintro a b ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem marked_of_cmp {σ' : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ' ty) (i : Fin Fu.n)
    {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P)
    {s : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) (h2 : ∀ z, h z ∈ u.Λ ↔ z ∈ P.range) :
    Marked o u (Fu.Di i) (Fu.t i) (h.toLinearMap.toAddMonoidHom.comp P) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y := fun x y h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨h.injective.comp hP.2.1, fun z => ?_, fun a => ?_, fun a ha => inj _ _ ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [h2]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, congrArg h ha⟩, fun ⟨a, ha⟩ => ⟨a, h.injective ha⟩⟩
  · refine ⟨(h.toLinearMap ∘ₗ LinearMap.mulLeft ℂ (fun k => ty k (a : E)) ∘ₗ h.symm.toLinearMap).restrictScalars ℝ,
      fun z => inj _ _ ?_, fun v => ?_⟩
    · obtain ⟨z, rfl⟩ := h.surjective z
      show (u.ex (h ((fun k => ty k (a : E)) * h.symm (h z)))).left ≫ _ = _
      rw [h.symm_apply_apply, h1, Over.comp_left, Category.assoc, m.act, ← Category.assoc, h1]
      exact congrArg (fun z => z.left) (Fu.ex_lin i P hP a z)
    · show h (P (a • v)) = h ((fun k => ty k (a : E)) * h.symm (h (P v)))
      rw [h.symm_apply_apply]
      exact congrArg h (funext (hP.1 a v))
  · have e : (l.M : ℝ)⁻¹ • (h.toLinearMap.toAddMonoidHom.comp P) (Fu.t i a) = h ((l.M : ℂ)⁻¹ • P (Fu.t i a)) := by
      rw [map_smul, ← Complex.coe_smul]
      push_cast
      rfl
    rw [e, h1, ← Fu.ex_eta i P hP a ha, m.eta]
    rfl

theorem vec_eq {e : c.F →+* ℂ} {g₀ : ℕ} {en : Fin g₀ ≃ Pad.Letter D} (Fu : Fam Xo c e en) (i : Fin Fu.n)
    {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c e (en j).1) P)
    {y : Sp ℂ ⟶ Xo.XF c} (hy : y ≫ toX Xo c = Fu.u i P)
    {s : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ (y ≫ toX Xo c)) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h4 : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v → (u.IsDiff (h w) v ↔
      IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)))
    {v₀ : Sp (DualNumber ℂ) ⟶ Y.oF.t.G.left} {v₁ : epsAt y ⟶ Y.oF.t.G} {v' : epsR ℂ ⟶ o.t.G} {w : Fin g₀ → ℂ}
    {V : Fin g → ℂ} (k1 : v₀ ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (k2 : v₁.left ≫ Y.m.φ = v₀ ≫ Y.m.φ)
    (k3 : IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Y.m0.toSABMap.φ))
    (k4 : v'.left ≫ m.toSABMap.φ = v₁.left ≫ Y.m0.toSABMap.φ) (k5 : u.IsDiff V v') : V = h w := by
  obtain rfl : v₀ = v₁.left := Y.m.cart.1.hom_ext k2.symm (k1.trans (Over.w v₁).symm)
  obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g₀ _ Fu i P hP
  have ht := t1 _ _ k3
  have hv : IsTangent v' := by
    have := (OpenReg.tan_iff m.toSABMap (x := 𝟙 _) ((Category.id_comp _).trans hy) (w := v'.left)
      ((Over.w v').trans (Category.comp_id _).symm)).1 (k4 ▸ ht)
    refine this.2.trans ?_
    rw [Hom.one_def]
    simp
  obtain ⟨V, rfl⟩ := h.surjective V
  have := (h4 V v' hv).1 k5
  rw [k4] at this
  rw [(t3 _ ht).unique this k3]

theorem exists_data {U : Set (Xo.XF c)} {τ : E →+* ℂ} {e : c.F →+* ℂ} {g₀ : ℕ} {en : Fin g₀ ≃ Pad.Letter D}
    (Fu : Fam Xo c e en) {x : ∀ i, Hor.Idx D τ → (Fu.Di i).La}
    {hm : Fin Fu.n → Matrix (Hor.Idx D τ) (Hor.Idx D τ) E} {σb : RuleY Y} {σ : RuleU Xo c} {κ : ℂ}
    (hτ : τ (H.rt : E) = H.rt0) (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) (hres : Restricts Y U τ σb σ)
    (hval : ∀ (a : CxFr Y e) v w i Q, Per Fu a i Q → FrY Y (compactOf Y U) τ e a.1.1 v w → Match τ a.2 v w →
      σb ℂ a.1.1 v w = κ * perVal c e τ (x i) (hm i) Q)
    {y : Sp ℂ ⟶ Xo.XF c} {v w} (hf : FrU Xo c U τ e y v w)
    {s : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ (y ≫ toX Xo c)) {g : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {V : Fin D.p → Fin g → ℂ} {W₀ : Fin D.q → Fin g → ℂ} (hV : IsVecs u m.toSABMap.φ v V)
    (hW₀ : IsVecs u m.toSABMap.φ w W₀) :
    ∃ (i : Fin Fu.n) (P₀ : (Fu.Di i).La →+ (Fin g₀ → ℂ)) (P : (Fu.Di i).La →+ (Fin g → ℂ))
      (W : Pad.Letter D → Fin g → ℂ) (Q : (Fu.Di i).La →+ (Pad.Letter D → ℂ)),
      IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c e (en j).1) P₀ ∧ y ≫ toX Xo c = Fu.u i P₀ ∧
      Marked o u (Fu.Di i) (Fu.t i) P ∧ PerData c e (Fu.Di i) Hm P W Q ∧ MatchVec τ W V W₀ ∧
      GoodPer c e τ (x i) (hm i) Q ∧ σ ℂ y v w = κ * perVal c e τ (x i) (hm i) Q := by
  obtain ⟨vb, wb, hfb, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ ℂ e y).1 v w hf
  obtain ⟨f₀⟩ := EigLoc.exists_eigFrame E H D l Xo c O β Y ℂ e (y ≫ Y.jQ) hfb.1
  obtain ⟨f, hmat⟩ := (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ _ ℂ e _ hfb.1 hfb.2.1 f₀).2 vb wb hfb
  let a : CxFr Y e := ⟨⟨y ≫ Y.jQ, hfb.1⟩, f⟩
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ toX Xo c) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hf.1, OpenReg.spMap_comp])
  obtain ⟨W, hW⟩ := exists_dirs (a := a) hP hu.symm rfl
  obtain ⟨b, rfl⟩ := dirs_basis (a := a) hP hu.symm rfl hW
  let Q := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hPQ : ∀ v, P v = ∑ z, Q v z • b z := fun v => (b.sum_equivFun (P v)).symm
  have hper : Per Fu a i Q := ⟨P, b, y, hP, hu.symm, rfl, hW, hPQ⟩
  have hgood := goodPer_of_per E H D l Xo c O β Y e g₀ en Fu τ a i Q _ _ hper (hx i)
  obtain ⟨h, h1, h2, h3, h4⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo _ g₀ _ Fu i P _ s o m g u Hm χ hP hu.symm hAH
  have hmk := marked_of_cmp Fu i hP hu.symm m u h h1 h2
  refine ⟨i, P, _, fun z => h (b z), Q, hP, hu.symm, hmk, ⟨hAH.1, hAH.2.1, ?_, h3,
    b.linearIndependent.map' h.toLinearMap h.ker, fun v => ?_, hgood.1⟩, ⟨fun j k hk => ?_, fun j k hk => ?_⟩, hgood, ?_⟩
  · rw [← u.full]
    exact congrArg _ (Set.ext fun z => (hmk.2.1 z).symm)
  · show h (P v) = _
    rw [hPQ, map_sum]
    simp only [map_smul]
  · obtain ⟨v₀, k1, k2, k3⟩ := hW ⟨τ, k⟩
    obtain ⟨v₁, l1, l2⟩ := sv j
    obtain ⟨v', n1, n2⟩ := hV j
    exact vec_eq Fu i hP hu.symm m u h h4 k1 (l2.trans ((hmat.1 j k hk).trans k2.symm)) k3 (n1.trans l1.symm) n2
  · obtain ⟨v₀, k1, k2, k3⟩ := hW ⟨conjEmb τ, k⟩
    obtain ⟨v₁, l1, l2⟩ := sw j
    obtain ⟨v', n1, n2⟩ := hW₀ j
    exact vec_eq Fu i hP hu.symm m u h h4 k1 (l2.trans ((hmat.2 j k hk).trans k2.symm)) k3 (n1.trans l1.symm) n2
  · exact (hres ℂ e y v w vb wb hf hfb sv sw).symm.trans (hval a vb wb i Q hper hfb hmat)

theorem isFlatAt_of_eq_perVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (e : c.F →+* ℂ) (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en) (x : ∀ i, Hor.Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Hor.Idx D τ) (Hor.Idx D τ) E) (σb : RuleY Y) (σ : RuleU Xo c) (κ : ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → Restricts Y U τ σb σ → (∀ (a : CxFr Y e) v w i Q, Per Fu a i Q → FrY Y (compactOf Y U) τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * perVal c e τ (x i) (hm i) Q) → IsFlatAt Xo c U τ σ e := by
  intro E _ _ _ H D l Xo c O _ β Y U τ e g₀ en Fu x hm σb σ κ B io hU hio hr hs hτ hx hres hval
    y y' v w v' w' hf hf' o o' m m' g g' u u' Hm Hm' χ χ' φ V W₀ V' W₀' z Δ Δ' hAH hAH' hφ a1 a2 a3 a4 hΔ hΔ'
  obtain ⟨i, P₀, P, W, Q, p1, p2, p3, p4, p5, p6, p7⟩ := exists_data Fu hτ hx hres hval hf m hAH a1 a2
  obtain ⟨i', P₀', P', W', Q', q1, q2, q3, q4, q5, q6, q7⟩ := exists_data Fu hτ hx hres hval hf' m' hAH' a3 a4
  obtain rfl : i = i' := GlobalTheory.T.complexPoints_component_same_periodSpace E H D l Xo c O β Y U e g₀ _ Fu i i' P₀ P₀' y y' B io hU hio hr hs hf.1 hf'.1
    hf.2.1 hf'.2.1 p1 q1 p2 q2
  obtain ⟨gm, hlev, hgm⟩ := exists_lev hφ (Fu.t_surj i) p3 q3
  have hiso : IsIsom (Fu.Di i) gm := fun a b => by
    have := hφ.2.2.1 (P a) (P b)
    rw [hgm, hgm, p4.2.2.2.1, q4.2.2.2.1] at this
    exact_mod_cast this
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := q4
  have hpd : PerData c e (Fu.Di i) Hm' (P'.comp gm.toLinearMap.toAddMonoidHom) W'
      (Q'.comp gm.toLinearMap.toAddMonoidHom) :=
    ⟨r1, r2, by rw [← r3]; exact congrArg _ (gm.surjective.range_comp P'), fun a b => (r4 _ _).trans (congrArg _ (hiso a b)),
      r5, fun a => r6 _, fun a b k => (congrArg (Q' · k) (gm.map_smul a b)).trans (r7 a _ k)⟩
  have key := perVal_mul_wedgeCoord E H D l c e τ (Fu.Di i) (x i) (hm i) g g' Hm Hm' P _ W W' Q _ φ V W₀ V' W₀' z Δ Δ'
    hτ (hx i) p4 hpd p6 (HorIso.perVal_isom E H D l c e _ τ _ _ Q' gm (hx i) q6 hiso).1 hgm p5 q5 hΔ hΔ'
  rw [perVal_isLev (hx i) q6 hiso hlev] at key
  rw [p7, q7, _root_.mul_assoc, key, _root_.mul_assoc]

end GlobalTheory.DetLine.FlatMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GenericUnitary

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TempSatUnr

open GlobalTheory.TempSat

theorem isSpherical_of_hasSatGL {E : Type} [Field E] [NumberField E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V}
    {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w ρ S) : GlobalTheory.SmGL.IsSpherical ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w a :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]
  exact hS.1

end GlobalTheory.TempSatUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_comp_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hf hg
  obtain ⟨-, hflf, -, hrf⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨-, hflg, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K B C g hg
  have : IsFinite f.hom.left := hf.1
  have : Surjective f.hom.left := hf.2
  have : IsFinite g.hom.left := hg.1
  have : Surjective g.hom.left := hg.2
  have hc : IsIsogeny (f ≫ g) := by
    refine ⟨?_, ?_⟩
    · rw [comp_hom, Over.comp_left]; infer_instance
    · rw [comp_hom, Over.comp_left]; infer_instance
  refine ⟨hc, ?_⟩
  have hdg : deg g = g.hom.left.finrank C.origin := if_pos hg
  have hdc : deg (f ≫ g) = (f ≫ g).hom.left.finrank C.origin := if_pos hc
  rw [hdc, hdg, comp_hom, Over.comp_left]
  exact GlobalTheory.FinrankComp.finrank_comp_of_const f.hom.left g.hom.left (deg f) hrf C.origin

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetAnalyticOfPeriodsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_analytic_of_periods : GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.HilbertBlumenthal → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetAnalytic := by
  first | exact @GlobalTheory.LatJet.An.jetAnalytic_of_periods | exact GlobalTheory.LatJet.An.jetAnalytic_of_periods | (intros; apply GlobalTheory.LatJet.An.jetAnalytic_of_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionLocallyCutOutByIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : OActN D.O A) (z : S),
  ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'), spMap f ≫ hU.fromSpec ≫ s = spMap β →
      (LieHer b act β (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.lieHer_ideal) | (exact GlobalTheory.UPel.HT.LieLin.lieHer_ideal) | (intros; apply GlobalTheory.UPel.HT.LieLin.lieHer_ideal  <;> assumption)
end

