import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBase
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.BaseAcris

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

def invS (h : IsBase l A) : A.A →+* Ob l := (RingEquiv.ofBijective A.s h).symm.toRingHom

theorem invS_comp (h : IsBase l A) : (invS A h).comp A.s = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).symm_apply_apply x

theorem comp_invS (h : IsBase l A) : A.s.comp (invS A h) = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).apply_symm_apply x

theorem map_xi_invS (h : IsBase l A) : WittVector.map (invS A h) A.xi = xi0 l := by
  rw [xi, sW, ← wmap_comp, invS_comp, wmap_id]

theorem awayW_left (h : IsBase l A) (y : WL l (Ob l)) : awayW (invS A h) (awayW A.s y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, invS_comp, awayW_id]; rfl

theorem awayW_right (h : IsBase l A) (y : WL l A.A) : awayW A.s (awayW (invS A h) y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, comp_invS, awayW_id]; rfl

theorem awayW_inv_mem (h : IsBase l A) {y : WL l A.A} (hy : y ∈ A.Acr0) :
    awayW (invS A h) y ∈ ACris.ACrisZero ℂ_[l] l := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have e := awayW_dpw (invS A h) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [map_xi_invS] at e
    exact Set.mem_of_eq_of_mem e (ACris.dpow_mem xi0_mem k)
  | algebraMap x => rw [awayW_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem acrisZero_bijective_of_isBase (h : IsBase l A) : Function.Bijective A.cris0 := by
  constructor
  · intro x y hxy
    have e : awayW A.s x.1 = awayW A.s y.1 := congrArg Subtype.val hxy
    have e' := congrArg (awayW (invS A h)) e
    rw [awayW_left, awayW_left] at e'
    exact Subtype.ext e'
  · intro y
    exact ⟨⟨awayW (invS A h) y.1, awayW_inv_mem A h y.2⟩, Subtype.ext (awayW_right A h y.1)⟩

theorem sW_bijective (h : IsBase l A) : Function.Bijective A.sW :=
  Function.bijective_iff_has_inverse.2 ⟨WittVector.map (invS A h),
    fun x => by
      change WittVector.map (invS A h) (WittVector.map A.s x) = x
      rw [← wmap_comp, invS_comp, wmap_id],
    fun x => by
      change WittVector.map A.s (WittVector.map (invS A h) x) = x
      rw [← wmap_comp, comp_invS, wmap_id]⟩

theorem oC_bijective (h : IsBase l A) : Function.Bijective A.oC := by
  have hs := sW_bijective A h
  have hth := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hth y
    rw [oC_theta0] at hy
    have hm : A.sW x ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := hs.2 c
    have e : x = c' * xi0 l := hs.1 (by rw [map_mul, ← hc]; rfl)
    have : x ∈ RingHom.ker (theta0 l) := by
      rw [e]; exact Ideal.mul_mem_left _ _ xi0_mem
    exact this
  · intro u
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨x, rfl⟩ := hs.2 w
    exact ⟨theta0 l x, A.oC_theta0 x⟩

theorem mem_map_of_evalₐ_eq_zero (B : Type) [CommRing B] (π : B) (n : ℕ)
    (a : AdicCompletion (Ideal.span {π}) B) (h : AdicCompletion.evalₐ (Ideal.span {π}) n a = 0) :
    a ∈ (Ideal.span {π} ^ n).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
  rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    ← AdicCompletion.factor_evalₐ_eq_eval _ a (by simp), h, map_zero]

theorem cris_surjective (h : IsBase l A) (n : ℕ) : Function.Surjective (A.cris n) := by
  intro u
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨y, rfl⟩ := (acrisZero_bijective_of_isBase A h).2 w
  exact ⟨AdicCompletion.of _ _ y, A.cris_of n y⟩

theorem cris_natCast_pow (n : ℕ) : A.cris n ((l : Acris l) ^ n) = 0 := by
  rw [map_pow, map_natCast, pow_l_acr]

theorem ker_cris (h : IsBase l A) (n : ℕ) :
    RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : Acris0 l)}) n a)
    have e : A.cris n a = A.mkAcr n (A.cris0 y) := by
      simp only [cris, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hy,
        Ideal.Quotient.lift_mk]
    rw [RingHom.mem_ker, e] at ha
    have hm : A.cris0 y ∈ Ideal.span {(l : A.Acr0) ^ n} := Ideal.Quotient.eq_zero_iff_mem.1 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := (acrisZero_bijective_of_isBase A h).2 c
    have e2 : y = c' * (l : Acris0 l) ^ n := (acrisZero_bijective_of_isBase A h).1 (by
      rw [map_mul, map_pow, map_natCast, hc])
    have hz : Ideal.Quotient.mk (Ideal.span {(l : Acris0 l)} ^ n) y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by
        rw [e2, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [hz] at hy
    have hk : a ∈ (Ideal.span {(l : Acris0 l)} ^ n).map (algebraMap (Acris0 l) (Acris l)) := by
      exact mem_map_of_evalₐ_eq_zero _ _ n a hy.symm
    rw [ACris.map_span_p_pow, Ideal.span_singleton_pow] at hk
    exact hk
  · rw [Ideal.span_singleton_le_iff_mem]
    exact cris_natCast_pow A n

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A →
    (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧
      ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} :=
  fun A h => ⟨⟨acrisZero_bijective_of_isBase A h, oC_bijective A h⟩, fun n => ⟨cris_surjective A h n, ker_cris A h n⟩⟩

end GlobalTheory.CompanionTheory.BaseAcris
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinOfBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

variable {R : Type} [CommRing R] {X : Scheme.{0}}

private theorem res_res_lemma {A B C : X.Opens} (f : B ⟶ A) (g' : C ⟶ B) (s : Γ(X, A)) :
    X.presheaf.map g'.op (X.presheaf.map f.op s) = X.presheaf.map (g' ≫ f).op s := by
  rw [op_comp, Functor.map_comp]
  rfl

theorem eq_of_res_affine (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op b) : a = b := by
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i : {V : X.affineOpens // V.1 ≤ W} => i.1.1) W
    (fun i => homOfLE i.2)
  · intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X) hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    exact h i.1 i.2

theorem exists_global (g : ∀ U : X.affineOpens, Γ(X, U.1))
    (hg : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (g U) = g V) :
    ∃ t : Γ(X, ⊤), ∀ U : X.affineOpens,
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t = g U := by
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun i : X.affineOpens => i.1) g := by
    intro i j
    apply eq_of_res_affine
    intro V hV
    rw [res_res_lemma, res_res_lemma]
    exact (hg i V (hV.trans inf_le_left)).trans (hg j V (hV.trans inf_le_right)).symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i : X.affineOpens => i.1) ⊤
    (fun i => homOfLE le_top) (by
      intro x _
      obtain ⟨V, hV, hxV, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X)
          (show x ∈ (⊤ : X.Opens) from trivial)
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨⟨V, hV⟩, hxV⟩) g hcompat
  exact ⟨t, ht⟩

theorem algebraMap_sec (s : X ⟶ Sp R) (U : X.Opens) (r : R) :
    algebraMap R (Sec s U) r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl

theorem stein_of_bijective (s : X ⟶ Sp R) (h : Function.Bijective s.appTop.hom) : Stein (OAff s) := by
  have key : ∀ (r : R) (U : X.affineOpens),
      (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) (op U) = X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r U
    exact algebraMap_sec s U.1 r
  refine ⟨?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hg : ∀ (U V : X.affineOpens) (hUV : V.1 ≤ U.1),
          X.presheaf.map (homOfLE hUV).op (y (op U)) = y (op V) := by
        intro U V hUV
        have e := congrFun (congrFun (congrFun hy (op U)) (op V)) (homOfLE (show V ≤ U from hUV)).op
        have e' : (show Γ(X, V.1) from y (op V)) - X.presheaf.map (homOfLE hUV).op (y (op U)) = 0 := e
        exact (sub_eq_zero.mp e').symm
      obtain ⟨t, ht⟩ := exists_global (fun U => y (op U)) hg
      obtain ⟨x, hx⟩ := h.2 t
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩
      funext T
      have hxinv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
        congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
      have e1 := key ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) T.unop
      rw [hxinv, hx] at e1
      exact e1.trans (ht T.unop)
    · rintro ⟨r, rfl⟩
      funext T T' φ
      have hc : (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) =
          (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' := (GlobalTheory.CatCoh.mp (OAff s) φ).commutes r
      show (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' -
          (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) = 0
      rw [hc, sub_self]
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have e : s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
      apply eq_of_res_affine
      intro V hV
      rw [map_zero]
      have e2 := congrFun hr (op V)
      rw [key] at e2
      exact e2
    have e3 := h.1 (e.trans (map_zero _).symm)
    have hr2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
      congrArg (fun f => CommRingCat.Hom.hom f r) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
    rw [e3, map_zero] at hr2
    exact hr2.symm

theorem stein_holds : SteinSt := by
  unfold MainStatements.Hodge.SteinSt MainStatements.Hodge.AllAb
  intro R _ A _ g hA _
  exact stein_of_bijective A.hom (GlobalTheory.globalFns_holds (Sp R) A hA)

end GlobalTheory.CompanionTheory.Hodge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.MassTest

theorem exists_bump {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set W}
    (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ φ : W → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ U ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ 0 ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨f, hf1, hf0, hfc, hfr⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x))
    (isOpen_interior (s := K)).isClosed_compl (by simpa using hxK)
  have hsupp : Function.support f ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hf0 (fun h => hyK (interior_subset h)))
  have hg : Continuous fun X => ENNReal.ofReal (f X) := ENNReal.continuous_ofReal.comp f.continuous
  refine ⟨f, f.continuous, hfc, fun X => (hfr X).1, ?_, ?_, ?_⟩
  · exact (closure_minimal hsupp hK.isClosed).trans hKU
  · intro h0
    have hpos : 0 < ν {X | ENNReal.ofReal (f X) ≠ 0} := by
      refine IsOpen.measure_pos ν (isOpen_ne_fun hg continuous_const) ⟨x, ?_⟩
      have : f x = 1 := hf1 (Set.mem_singleton x)
      simp [this]
    exact hpos.ne' (ae_iff.1 ((lintegral_eq_zero_iff hg.measurable).1 h0))
  · exact (f.continuous.integrable_of_hasCompactSupport hfc).lintegral_lt_top.ne

theorem exists_compactOpen {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W]
    [TotallyDisconnectedSpace W] [MeasurableSpace W] (ν : Measure W) [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {U : Set W} (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ A : Set W, IsCompact A ∧ IsOpen A ∧ A ⊆ U ∧ ν A ≠ 0 ∧ ν A ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := W)).exists_subset_of_mem_open hxK
    isOpen_interior
  have hCc : IsCompact C := hK.of_isClosed_subset hC.1 (hCK.trans interior_subset)
  exact ⟨C, hCc, hC.2, (hCK.trans interior_subset).trans hKU, (hC.2.measure_pos ν ⟨x, hxC⟩).ne',
    hCc.measure_lt_top.ne⟩

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem gramR_ratTup_apply (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) (a c : Fin n) :
    gramR R σ J (ratTup R Y) a c = inclR R (gramE σ J Y a c) := by
  simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 2) (Fin 2) E}
    (hA : Aniso σ J) : ∃ X : Fin 1 → Fin 2 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := fun h => one_ne_zero (congrFun (hA _ h) 0)
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 2) (Fin 2) E) :
    IsOpen {X : Fin 1 → Fin 2 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 2 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 2 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 2 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 2 A ≠ 0 ∧ coordW R b lam 1 2 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hA (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 2 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 2 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hA (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 2 (A0 v) := by
    unfold vol
    congr 1
    exact Finset.prod_congr rfl fun v hvS => by simp [hvS]
  refine ⟨φ, fun v => if v ∈ S then A0 v else latV b v, ⟨h1, h2, h3, h4, ?_, ?_⟩, ?_, ?_⟩
  · intro v hvS
    simp only [hvS, if_true]
    exact ⟨hc v, ho v, hs v⟩
  · intro v hvS
    simp [hvS]
  · rw [hv]
    exact mul_ne_zero h5 (Finset.prod_ne_zero_iff.2 fun v _ => hn v)
  · rw [hv]
    exact ENNReal.mul_ne_top h6 (ENNReal.prod_ne_top fun v _ => ht v)

end GlobalTheory.CompanionTheory.SW.MassTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedSumLimit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem tsum_unitVec_eq {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (h : F → ℝ) :
    ∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}, h (x.1 ()) =
      ∑' x : F, (IntOut T).indicator h x := by
  let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ (IntOut T) :=
    (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
      constructor
      · intro hx v hv
        exact hx v hv ()
      · intro hx v hv i
        exact hx v hv)
  rw [← tsum_subtype (IntOut T) h]
  exact e.tsum_eq (fun y : IntOut T => h y.1)

theorem tsum_eq_zero_add_of_finset {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' x : F, h x = h 0 + ∑' β : {β : F // β ≠ 0}, h β.1 := by
  rw [tsum_ne_zero_eq_sum h B hB hh, tsum_eq_sum (s := insert 0 B) ?_, Finset.sum_insert (fun h0 => hB 0 h0 rfl)]
  intro x hx
  simp only [Finset.mem_insert, not_or] at hx
  exact hh x hx.1 hx.2

theorem integral_unitVec_eq {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → ℝ) :
    ∫ y, f (y ()) ∂(Measure.pi fun _ : Unit => μ) = ∫ y, f y ∂μ :=
  (measurePreserving_funUnique μ Unit).integral_comp' (g := f)

theorem tendsto_truncSum : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by
  intro hE hC F _ _ hF θ hθ li lam hli hlam T G ψ hG hGc hψ
  have hlocI : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : LocallyCompactSpace (Ainf F) := hlocI.2.1
  have : SecondCountableTopology (Ainf F) := hlocI.2.2.1
  have := hli.1
  have : SigmaFinite li := inferInstance
  have hsf : ∀ v, SigmaFinite (lam v) := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    have : LocallyCompactSpace (Fv F v) := hloc.2.1
    have : SecondCountableTopology (Fv F v) := hloc.2.2.1
    have := (hlam v).1
    infer_instance
  have key := hE F hF θ hθ li lam hli hlam Unit T (fun y => G (y ())) (fun v y => ψ v (y ()))
    (hG.comp (continuous_apply ())) (hGc.comp_homeomorph (Homeomorph.funUnique Unit (Ainf F)))
    (fun v hv => ⟨(hψ v hv).1.comp (continuous_apply ()),
      (hψ v hv).2.comp_homeomorph (Homeomorph.funUnique Unit (Fv F v))⟩)
  rw [integral_unitVec_eq li G,
    Finset.prod_congr rfl (fun v _ => haveI := hsf v; integral_unitVec_eq (lam v) (ψ v))] at key
  simp only [Fintype.card_unit, mul_one] at key
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hpow : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0))) :=
      ((continuous_pow _).mul continuous_const).tendsto 0
    rw [zero_pow hd.ne', zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsub := key.sub hpow
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc (fun v hv => (hψ v hv).2) ε hε
  have h0mem : (0 : F) ∈ IntOut T := fun v _ => by
    rw [map_zero]
    exact zero_mem _
  have e := (tsum_unitVec_eq T (fun x => G (θ ε * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x))).trans (tsum_eq_zero_add_of_finset _ B hB hh)
  rw [Set.indicator_of_mem h0mem] at e
  rw [e]
  simp only [truncSum, map_zero, mul_zero]
  ring

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

