import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem mInt_half {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : Continuous g) :
    mInt A Φ (fun x => g x / 2) = mInt A Φ g / 2 := by
  have h0 := mIntegrableCont A Φ hΦ (fun _ => 0) continuous_const
  have h1 := mIntLinear A Φ hΦ 1 (fun _ => 0) (fun _ => 0) h0 h0
  have h2 := mIntLinear A Φ hΦ (1 / 2) g (fun _ => 0) (mIntegrableCont A Φ hΦ g hg) h0
  have e1 : (fun x => 1 / 2 * g x + 0) = fun x => g x / 2 := funext fun x => by ring
  simp only [mul_zero, add_zero] at h1
  rw [e1] at h2
  linarith

theorem mInt_cons_ofFun_symm {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] {A : FinHolAtlas (e + 1) (CxPts p σ)} (hA : IsAlgAtlas A)
    (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y) :
    mInt A (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).φ.locPot) v =
      mInt A (fun i => ((Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) i).φ.locPot) u := by
  have hpot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 N.cInf).isPotential hA
  have hsm (a : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) : A.Smooth fun y => a y / 2 := fun j =>
    ((hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1 fun y _ => ha y) j).div_const 2
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      mInt A (Fin.cons (LocPot.ofFun fun y => a y / 2) fun i => (L i).φ.locPot) (fun y => b y / 2) =
      mInt A (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).φ.locPot) b / 2 := by
    rw [← mInt_half A _ (fun i => hpot _) b (continuous_iff_continuousAt.2 fun y => (hb y).continuousAt)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun _ _ _ => rfl
    · exact fun _ _ _ => rfl
  have h := byPartsSymm A _ _ (hsm v hv) (hsm u hu) (fun i => (L i).φ.locPot) fun i => hpot _
  rw [key u v hu hv, key v u hv hu] at h
  linarith

theorem int_cons_ofFun_symm : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hproj hdim L u v hu hv
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hproj hdim ⊥
      (by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot]; exact Set.notMem_empty _)
  haveI := hsm
  haveI : CompactSpace (CxPts (π ≫ p) σ) := CxPts.compactSpace σ hprojY
  haveI : T2Space (CxPts (π ≫ p) σ) := CxPts.t2Space_cxPts_of_isProjOver σ hprojY
  haveI : SecondCountableTopology (CxPts (π ≫ p) σ) := CxPts.secondCountableTopology_of_isProjOver σ hprojY
  have hA : IsAlgAtlas (AnRead.all (π ≫ p) σ (e + 1)).finAtlas := AnRead.isAlgAtlas_finAtlas _
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hisoY := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      Mix.int (Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) b =
      mInt (AnRead.all (π ≫ p) σ (e + 1)).finAtlas (fun i => ((Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z))
        fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl : Fin (e + 1) → MLine (π ≫ p) σ) i).φ.locPot)
        (fun z => b (ptMap π rfl σ z)) := by
    have hbc : Continuous b := continuous_iff_continuousAt.2 fun y => (hb y).continuousAt
    have hbc' : Continuous fun z : CxPts (π ≫ p) σ => b (ptMap π rfl σ z) :=
      continuous_iff_continuousAt.2 fun z => ((hb _).pull π rfl).continuousAt
    have h1 := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hproj hdim hprojY π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) (Fin.cons (MLine.ofFun a ha) L) b hbc.measurable).2
    rw [hdeg, Nat.cast_one, one_mul] at h1
    have h2 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hprojY (e + 1)
      (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).pull π rfl)
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      (fun i => Fin.cases (hiso.2.2.2.1 a ha) (fun j => hisoY.1 _) i)
    have h3 := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ (e + 1) _ hA
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      _ hbc'.measurable
    rw [← h1, ← h3.2 (h3.1.2 (mIntegrableCont _ _
      (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (MLine.cInf _)).isPotential hA) _ hbc'))]
    simp only [Mix.int, h2]
  rw [key u v hu hv, key v u hv hu]
  exact mInt_cons_ofFun_symm hA _ _ _ _ _

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem exists_qkPt_tautPt : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → (∀ i, s i ≠ 0) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ), ∃ p : QkPt D F n, p.y = e.symm a ∧ TautPt T ω s ε n D e β ββ w F a p.g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF hs F _ _ a
  have hex := fun b => GlobalTheory.T.exists_tautological_point_torus_extension T ε n V D ω s e β ββ w hB hF hs F b
  let f : (Fin T.r → ℤ) → GtPtF D F := fun b => Classical.choose (hex b)
  have hf : ∀ b, TautPt T ω s ε n D e β ββ w F b (f b) := fun b => Classical.choose_spec (hex b)
  have hadd := GlobalTheory.T.tautological_point_torus_extension_add T ε n V D ω s e β ββ w hB hF F
  have hzi := GlobalTheory.T.tautologicalPoint_zero_and_period T ε n V D ω s e β ββ w hB hF F
  refine ⟨⟨e.symm a, f a, ⟨f (((n : ℕ) : ℤ) • a), ?_, ?_⟩⟩, rfl, hf a⟩
  · refine ⟨fun i => f (((i : ℕ) : ℤ) • a), ?_, ?_, rfl⟩
    · apply (hzi _).1
      have h0 : (((0 : Fin (n + 1)) : ℕ) : ℤ) • a = 0 := by simp
      dsimp only
      rw [h0]
      exact hf 0
    · intro i
      have h1 : ((i.succ : ℕ) : ℤ) • a = ((i.castSucc : ℕ) : ℤ) • a + a := by
        simp [add_smul]
      have h3 := hf (((i.succ : ℕ) : ℤ) • a)
      rw [h1] at h3
      have := hadd _ _ _ _ _ (hf (((i.castSucc : ℕ) : ℤ) • a)) (hf a) h3
      simpa only [h1] using this
  · apply (hzi _).2
    rw [e.apply_symm_apply]
    exact hf _

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArc
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerPoly

open scoped CategoryTheory.MonObj in

theorem exists_transfer_iff {S S' S0 : Scheme.{0}} {G : Over S} {G' : Over S'} {G0 : Over S0} [GrpObj G] [GrpObj G']
    [GrpObj G0] {f : S' ⟶ S} {f0 : S' ⟶ S0} {φ : G'.left ⟶ G.left} {φ0 : G'.left ⟶ G0.left}
    (h : IsGrpPullback G' G f φ) (h0 : IsGrpPullback G' G0 f0 φ0) (q : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} {y0 : Sp ℂ ⟶ S0}
    (hy : q ≫ f = y) (hy0 : q ≫ f0 = y0) {g : ℕ} (ex0 : (Fin g → ℂ) → (Over.mk y0 ⟶ G0))
    (hadd : ∀ z w, ex0 (z + w) = ex0 z * ex0 w)
    (hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G0.left from (ex0 z).left))) :
    ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ G), (∀ z w, ex (z + w) = ex z * ex w) ∧
      IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (ex z).left)) ∧
      (∀ (d : Fin g → ℂ) (w : Sp (DualNumber ℂ) ⟶ G'.left),
        w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ q →
        IsDerivAt0 (fun z => (ex0 z).left) d (w ≫ φ0) → IsDerivAt0 (fun z => (ex z).left) d (w ≫ φ)) ∧
      ∀ z, ex z = 1 ↔ ex0 z = 1 := by
  subst hy hy0
  let ex' : (Fin g → ℂ) → (Over.mk q ⟶ G') := fun z =>
    Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)
  have e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z := fun z =>
    Over.OverMorphism.ext (h0.1.lift_fst _ _ _)
  have e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left := fun z => h0.1.lift_fst _ _ _
  have e1 : ∀ z, (ex' z).left ≫ G'.hom = q := fun z => Over.w (ex' z)
  have inj0 : Function.Injective (pushHom h0 (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have inj : Function.Injective (pushHom h (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t := fun t =>
    HolHom.holAt_of_isPullback h0.1
      (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t))
      (by simp only [e1]; exact HolHom.holAt_const _ _)
  refine ⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z => ⟨fun hz => ?_,
    fun hz => ?_⟩⟩
  · have : ex' (z + w) = ex' z * ex' w := inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)
    exact (congrArg _ this).trans (map_mul _ _ _)
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ
  · obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt d
    have h1 := hv.comp φ0
    simp only [e0'] at h1
    have h2 : v = w := h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd))
      ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)
    subst h2
    exact (HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)
  · have : ex' z = 1 := inj (hz.trans (map_one _).symm)
    rw [← e0, this]
    exact map_one _
  · have : ex' z = 1 := inj0 ((e0 z).trans (hz.trans (map_one _).symm))
    show pushHom h (Over.mk q) (ex' z) = 1
    rw [this]
    exact map_one _

def zComb {m : ℕ} {V : Type} [AddCommGroup V] (lam : Fin m → V) : (Fin m → ℤ) →+ V :=
  (Fintype.linearCombination ℤ lam).toAddMonoidHom

theorem zComb_apply {m : ℕ} {V : Type} [AddCommGroup V] (lam : Fin m → V) (n : Fin m → ℤ) :
    zComb lam n = ∑ j, n j • lam j := Fintype.linearCombination_apply ℤ lam n

theorem zComb_lattice {m g : ℕ} (lam : Fin m → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (hsp : Submodule.span ℝ (Set.range lam) = ⊤) :
    Function.Injective (zComb lam) ∧ DiscreteTopology (zComb lam).range ∧
      Submodule.span ℝ (Set.range (zComb lam)) = ⊤ := by
  refine ⟨fun n n' h => ?_, ?_, ?_⟩
  · rw [zComb_apply, zComb_apply] at h
    have h0 : ∑ j, ((n j - n' j : ℤ) : ℝ) • lam j = 0 := by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext j
    have := Fintype.linearIndependent_iff.1 hli _ h0 j
    exact sub_eq_zero.1 (by exact_mod_cast this)
  · let bas := Module.Basis.mk hli hsp.ge
    have hr : (zComb lam).range = (Submodule.span ℤ (Set.range bas)).toAddSubgroup := by
      ext x
      simp only [bas, AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Module.Basis.coe_mk, Module.Basis.mk_apply,
        Submodule.mem_span_range_iff_exists_fun, zComb_apply]
    rw [hr]
    exact (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range bas)))
  · refine eq_top_iff.2 (hsp.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [zComb_apply]
    simp [Pi.single_apply]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ v ∈ (U.X k).Λ, ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v hv R
  obtain ⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩ := hU
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · refine ⟨0, 0, Filter.Eventually.of_forall fun w _ τ i hτ => ?_⟩
    exfalso
    have hp0 := (hX k).1
    rcases hτ with ⟨_, hi⟩ | ⟨_, hi⟩ <;> omega
  have hoff : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z := by
    intro u hu hu0 s hb
    obtain ⟨hm1, -⟩ := hm u hu hu0
    have hm1' : GlobalTheory.AllWt.ptF (y u) ≫ Z.jQ = spMap (ψ u) ≫ x := hm1
    exact hb ⟨GlobalTheory.AllWt.ptF (y u) s, by rw [← hm1']; rfl⟩
  obtain ⟨T₀, m, lam, hT₀, hcont, hbas, hker, hgrow⟩ :=
    GlobalTheory.T.exists_continuous_period_basis_along_arc E H Dw l Xo c O β Z σ A φ x fr ψ r g e hσ hpq harc hoff
  obtain ⟨-, -, hxd, hxm, -⟩ := horb
  set T₁ := max T T₀ with hT₁def
  have hT₁ : ∀ w : ℂ, T₁ < w.im → T < w.im ∧ T₀ < w.im := fun w hw =>
    ⟨(le_max_left _ _).trans_lt hw, (le_max_right _ _).trans_lt hw⟩
  let B := {w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected
  have hdom : ∀ b : B, xx b ∈ (U.X k).dom := fun b => hxm b (hT₁ b b.2).1
  choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩
  clear hrest
  set a₀ := (φL k).symm ⟨v, hv⟩ with ha₀
  have hva : ((φL k a₀ : (U.X k).Λ) : Fin N → E) = v := by rw [ha₀, LinearEquiv.apply_symm_apply]
  have key : ∀ b : B, ∃ n : Fin m → ℤ, Pm b a₀ = zComb (lam b) n := fun b => by
    have hb := hT₀ b (hT₁ b b.2).2
    obtain ⟨_, hx1, hx2⟩ := hlift b (hT₁ b b.2).1
    obtain ⟨hm1, hm2⟩ := hm _ hb (Complex.exp_ne_zero _)
    have h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x := pullback.lift_fst _ _ _
    obtain ⟨ex, a1, a2, a3, a4⟩ := exists_transfer_iff Z.m.cart Z.m0.toSABMap.cart
      (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :)
      (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _)))
      (h0.trans (hx1.symm.trans (hpt b))) (F.ex (ik k) (Pm b)) (F.ex_add _ _ (hper b))
      (HolHom.isHolTo_ex F _ (hper b))
    have hk := hker b (hT₁ b b.2).2 ex a1 a2 (fun jj => by
      obtain ⟨w, w1, w2, w3⟩ := hm2 (e jj).1 (e jj).2
      have hd := hder b (e jj).1 (e jj).2
      rw [hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply] at hd
      exact w3 ▸ a3 _ w w1 hd) (Pm b a₀)
    obtain ⟨n, hn⟩ := hk.1 ((a4 _).2 ((F.ex_ker _ _ (hper b) _).2 ⟨a₀, rfl⟩))
    exact ⟨n, hn.trans (zComb_apply _ _).symm⟩
  choose n hn using key
  have hxc : Continuous fun b : B => xx b :=
    (hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict
  have hPc : ∀ z, Continuous fun b : B => Pm b z := fun z => continuous_pi fun jj => by
    simp only [hPm]
    exact PerLim.continuous_perFr _ hdom hxc _ _ _
  have hlc : ∀ j, Continuous fun b : B => lam b j := fun j =>
    (continuous_apply j).comp (hcont.comp_continuous continuous_subtype_val fun b => (hT₁ b b.2).2)
  have hZc : ∀ z, Continuous fun b : B => zComb (lam b) z := fun z => by
    simp only [zComb_apply]
    exact continuous_finset_sum _ fun j _ => (hlc j).const_smul (z j)
  let b₀ : B := ⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩
  have hconst : ∀ b, n b = n b₀ := fun b => by
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace (f := n)
      ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀
    obtain ⟨hi, hd, hs⟩ := zComb_lattice (lam b') (hbas b' (hT₁ b' b'.2).2).1 (hbas b' (hT₁ b' b'.2).2).2
    refine PerLim.eventually_eq_of_lattice (fun b : B => zComb (lam b)) hZc b' hi hd hs n ?_
    exact (hPc a₀).congr fun b => hn b
  obtain ⟨C, Bx, hC⟩ := hgrow R
  have hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) →
      ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i := by
    intro τ m hmτ
    obtain ⟨τ', rfl⟩ := Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ
    have h1 : m = Dw.mult τ' := by
      rw [hmτ, Datum.mult]
      exact if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl
    subst h1
    refine ⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2
    · rw [Equiv.apply_symm_apply]
      exact ⟨rfl, rfl⟩
  have hlet : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨
      (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ∃ jj : Fin g, relab c σ (e jj).1 = τ ∧ ((e jj).2 : ℕ) = i := by
    intro τ i hτ
    rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨s, -, hs⟩ := hidx τ (N - (U.X k).p0) (by
        rw [if_pos (((hX k).2 _).1 h1), (hX k).1, hN, Nat.add_sub_cancel])
      exact ⟨s ⟨i, h2⟩, hs _⟩
    · have hcc : NumberField.ComplexEmbedding.conjugate (conjEmb τ) = τ := RingHom.ext fun a => by
        simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]
      have hne : ¬ τ (H.rt : E) = H.rt0 := fun h =>
        ((U.X k).cmType (conjEmb τ)).1 h1 (by rw [hcc]; exact ((hX k).2 τ).2 h)
      obtain ⟨s, -, hs⟩ := hidx τ (U.X k).p0 (by rw [if_neg hne, (hX k).1])
      exact ⟨s ⟨i, h2⟩, hs _⟩
  refine ⟨(∑ j, (|n b₀ j| : ℝ)) * C, Bx, ?_⟩
  filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)]
    with w hw hR τ i hτ
  obtain ⟨jj, hj1, hj2⟩ := hlet τ i hτ
  have hP : perFr (U.X k) (xx w) v τ i = Pm ⟨w, hw⟩ a₀ jj := by
    rw [hPm, hva, hj1, hj2]
  rw [hP, hn, hconst, zComb_apply]
  have hl := hC w (hT₁ w hw).2 hR
  calc ‖(∑ j, n b₀ j • lam (⟨w, hw⟩ : B) j) jj‖ ≤ ‖∑ j, n b₀ j • lam (⟨w, hw⟩ : B) j‖ := norm_le_pi_norm _ _
    _ ≤ ∑ j, ‖n b₀ j • lam w j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (|n b₀ j| : ℝ) * ‖lam w‖ := Finset.sum_le_sum fun j _ => by
        rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs, ← Int.cast_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (by positivity)
    _ = (∑ j, (|n b₀ j| : ℝ)) * ‖lam w‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, (|n b₀ j| : ℝ)) * (C * w.im ^ Bx) :=
        mul_le_mul_of_nonneg_left hl (Finset.sum_nonneg fun j _ => by positivity)
    _ = _ := (mul_assoc _ _ _).symm

end GlobalTheory.ShFam.PerPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjective
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.PLSnc

theorem int_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Mix.int L (fun y => f y / 2) = Mix.int L f / 2 := by
  simp only [Mix.int, integral_div, sub_div]

theorem finsum_mult {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {B : LB X} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) {r : ℕ} {z : Fin r → X} (hz : Function.Injective z)
    (h : ∀ w : X, w ∉ nonzeroLocus s → Order.coheight w = 1 → ∃ a, w = z a) (g : X → ℝ) :
    ∑ᶠ w, ((divOfSec hB s hs).mult w : ℝ) * g w =
      ∑ a, ((((divOfSec hB s hs).mult (z a)).toNat : ℕ) : ℝ) * g (z a) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image z), Finset.sum_image fun a _ b _ e => hz e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (mult_divOfSec_nonneg _)]
  · intro w hw
    have h0 : (divOfSec hB s hs).mult w ≠ 0 := fun e => hw (by simp [e])
    obtain ⟨a, rfl⟩ := h w (fun e => notMem_supp_divOfSec.2 e (CartierDiv.mem_supp_of_mult_ne_zero h0))
      (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    simp

theorem poincareLelong_snc : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro F _ X _ _ p σ e hp hsm L M s hs hsnc u hu
  haveI : CharZero F := σ.charZero
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  let R := AnRead.all p σ (e + 1)
  have hA := R.isAlgAtlas_finAtlas
  generalize R.finAtlas = A at hA
  obtain ⟨r, z, hinj, hco, hT, hall, hl⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F X p (e + 1) hp hsm _ hsnc
  have hS := GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section F X p σ (e + 1) hp hsm A hA M s hs r z hinj hco hT hl
  choose B hB hBint using fun a => GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme F X (clos (z a)) p _ σ hp (closι (z a)) rfl e A hA
    (GlobalTheory.T.smooth_snc_component_closure_charZero F X p e hp hsm r z hl a)
  have pot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth R).1 N.cInf).isPotential hA
  have hv (y) : CInfAt (fun y => u y / 2) y :=
    ((hu y).const_mul (1 / 2)).congr (.of_forall fun z => by ring)
  have hvc : Continuous fun y => u y / 2 := continuous_iff_continuousAt.2 fun y => (hv y).continuousAt
  have key := poincareLelong A M.φ.locPot _ _ _ B (pot M)
    (M.φ.isSection_of_isAlgAtlas hA (R.secVal_mem_holSec s)) hS hB (fun y => u y / 2)
    ((hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y))
    (fun i => (L i).φ.locPot) fun i => pot _
  have e₁ : logNormSec M.φ.locPot (M.φ.locSec (secVal p σ s)) = M.logSec s := funext fun y => by
    rw [Weight.logNormSec_locSec, MLine.logSec]; ring
  have e₂ : Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      mInt A (Fin.cons (LocPot.ofFun fun y => u y / 2) fun i => (L i).φ.locPot) (M.logSec s) := by
    rw [(GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA _ _ (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1).2
      (GlobalTheory.T.integrable_logNormSection_mixedChernForms F X p σ _ hp hsm _ M s hs)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Weight.sameForm_ofFun A u
    · exact SameForm.refl _ _
  have e₃ : Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (fun y => u y / 2) =
      mInt A (Fin.cons M.φ.locPot fun i => (L i).φ.locPot) fun y => u y / 2 := by
    have h := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA (Fin.cons M L : Fin (e + 1) → MLine p σ) _ hvc.measurable
    rw [h.2 (h.1.2 (mIntegrableCont A _ (fun i => pot _) _ hvc))]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  have e₄ (a) : mInt (B a) (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val)
      ((fun y => u y / 2) ∘ Subtype.val) = cycInt L u (z a) / 2 :=
    (hBint a L _ hvc).trans (int_half _ _)
  rw [e₁, ← e₂, ← e₃, int_half] at key
  simp only [e₄] at key
  rw [key, finsum_mult M.φ.isLB s hs hinj (fun w hw => hall w hw), mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

end GlobalTheory.Mix.PLSnc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFG

theorem siegPre_descends_fg : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  intro g n hn hodd R _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R₀, β₀, A₀, _, P₀, lv₀, hft, hβ, hsym, hadd, hamp, hpb⟩ := GlobalTheory.SiegFGData.data g n hn hodd R β c hc
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hpb' := hpb
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := hpb
  have hpr : IsPrincipal A₀ P₀ :=
    GlobalTheory.PrincSubring.isPrincipal_of_subring g R R₀ c.A c.P A₀ P₀ φ φ₂ hsym hamp hφ ⟨s₁, s₂⟩ iso ((principal_iff c).1 hc)
  let u : (cycAway n)ˣ := Units.ofPowEqOne (zetaAway n) n (zetaAway_pow_self hn0) hn0
  have hζ : u ^ n = 1 := Units.ext (by simp [u])
  have hunit : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map β₀
  have hlevR : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := u) c
  have hlev₀ : IsLevel A₀ lv₀ :=
    GlobalTheory.LevelDescent.isLevel_of_subring g n R R₀ c.A A₀ φ (lvOf c) lv₀ (by omega) hunit hsym.1 hφ hl hadd hlevR
  have hsympR : IsSymplectic u (spMap β) c.A c.P (lvOf c) :=
    isSymplectic_of_translFixed (ζ := u) hn0 hζ (isUnit_natCast hn0) c (translFixed_of_ample c hc.1)
  have hsymp₀ : IsSymplectic u (spMap β₀) A₀ P₀ lv₀ :=
    GlobalTheory.SympDescent.isSymplectic_of_subring g n (cycAway n) R u R₀ (spMap β₀) c.A c.P (lvOf c) A₀ P₀ lv₀ (by omega) hζ hunit hsym hpr hlev₀
      c.isLB hpb' (by rw [← GlobalTheory.SiegelTypings.spMap_comp, hβ]; exact hsympR)
  let c₀ : SiegPre g n (zetaAway n) (spMap β₀) := ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀
  refine ⟨R₀, β₀, c₀, hft, hβ, (principal_iff c₀).2 hpr, (siegPB_iff c c₀ _).2 ?_⟩
  rw [show lvOf c₀ = lv₀ from lvOf_ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀]
  exact hpb'

end GlobalTheory.SiegFG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_uniformised_groups_uniformised_by_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  first | exact @GlobalTheory.MumProdUnifSum.main | exact GlobalTheory.MumProdUnifSum.main | (intros; apply GlobalTheory.MumProdUnifSum.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recognition_degData_labels_at_every_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.Recognition.pullDeg_induces | exact GlobalTheory.Mum.Recognition.pullDeg_induces | (intros; apply GlobalTheory.Mum.Recognition.pullDeg_induces <;> assumption)
end

