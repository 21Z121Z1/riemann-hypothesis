import Mathlib
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.GLnPowerSubgroups
import GroundTheory.AutomorphicForms.SphericalIntegral

-- bundled from GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
section
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

theorem eq_one_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : G →* {r : ℝ // 0 < r}) (hf : Continuous fun g => (f g : ℝ))
    {h : G} (hh : h ∈ H) : f h = 1 := by
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ m : ℕ, (f h : ℝ) ^ m ≤ M ∧ ((f h : ℝ)⁻¹) ^ m ≤ M := fun m => by
    have h1 := hM (h ^ m) (pow_mem hh m)
    have h2 := hM ((h⁻¹) ^ m) (pow_mem (inv_mem hh) m)
    rw [map_pow, Positive.val_pow, Real.norm_eq_abs, abs_of_pos (pow_pos (f h).2 m)] at h1
    rw [map_pow, map_inv, Positive.val_pow, Positive.coe_inv, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.2 (f h).2) m)] at h2
    exact ⟨h1, h2⟩
  refine Subtype.ext ?_
  rw [Positive.val_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 < (f h : ℝ)⁻¹ := (one_lt_inv₀ (f h).2).2 hlt
    obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).2 (not_le.2 hm)
  · obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).1 (not_le.2 hm)

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def normDet (w : InfinitePlace K) : GL (Fin n) w.Completion →* {r : ℝ // 0 < r} where
  toFun g := ⟨‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖, norm_pos_iff.2 (by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero)⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.det_mul]

theorem continuous_normDet (w : InfinitePlace K) :
    Continuous fun g : GL (Fin n) w.Completion => (normDet (n := n) w g : ℝ) :=
  (Continuous.matrix_det (Units.continuous_val (M := Matrix (Fin n) (Fin n) w.Completion))).norm

theorem norm_det_of_mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) : ‖(k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 := by
  have := eq_one_of_isCompact (isCompact_archCompact w) (normDet w) (continuous_normDet w) hk
  exact congrArg Subtype.val this

theorem norm_det_infAt_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact)
    (w : InfinitePlace K) : ‖(infAt w k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 :=
  norm_det_of_mem_archCompact (hk.1 w)

theorem infAt_diagUnits (w : InfinitePlace K) (f : Fin n → IdeleGroup K) :
    infAt w (diagUnits n f) = diagUnits n (fun i => infiniteProj w (f i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [infAt_apply, coe_diagUnits, coe_diagUnits, diagonal_apply, diagonal_apply]
  split_ifs
  · rw [coe_infiniteProj]
  · rfl

theorem infAt_diagUnits_posIdele (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    infAt w (diagUnits n fun i => posIdele (K := K) (r i) (hr i)) =
      diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) := by
  rw [infAt_diagUnits]
  congr 1
  funext i
  exact infiniteProj_posIdele (r i) (hr i) w

theorem norm_posRealToUnits (w : InfinitePlace K) {r : ℝ} (hr : 0 < r) :
    ‖((posRealToUnits w ⟨r ^ w.mult, pow_pos hr _⟩ : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have h := norm_posRealElem_pow w (pow_pos hr w.mult).le
  have hm : w.mult ≠ 0 := InfinitePlace.mult_ne_zero
  exact (pow_left_inj₀ (norm_nonneg _) hr.le hm).1 h

theorem norm_det_diagUnits_posRealToUnits (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ‖((diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) :
      GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion).det‖ = ∏ i, r i := by
  rw [coe_diagUnits, det_diagonal, norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_posRealToUnits w (hr i)

theorem prodEquiv_diagUnits_posIdele_snd (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (AdelicGLn.prodEquiv K n (diagUnits n fun i => posIdele (K := K) (r i) (hr i))).2 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_snd, coe_diagUnits, diagonal_apply]
  split_ifs with h
  · subst h
    refine RestrictedProduct.ext _ _ fun v => ?_
    have := posIdele_finite (K := K) (r a) (hr a) v
    exact this.trans (by simp; rfl)
  · rw [Units.val_one, Matrix.one_apply_ne h]
    rfl

end Reduction

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.ReductionSplitting
section
open NumberField IsDedekindDomain Topology Filter Set Matrix MeasureTheory
open scoped NumberField.AdeleRing RestrictedProduct ENNReal
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def rpowHom (e : ℝ) : {r : ℝ // 0 < r} →* {r : ℝ // 0 < r} where
  toFun s := ⟨s.1 ^ e, Real.rpow_pos_of_pos s.2 e⟩
  map_one' := Subtype.ext (Real.one_rpow e)
  map_mul' s t := Subtype.ext (Real.mul_rpow s.2.le t.2.le)

theorem continuous_rpowHom (e : ℝ) : Continuous (rpowHom e) :=
  (continuous_subtype_val.rpow_const fun s => Or.inl s.2.ne').subtype_mk _

variable (K) in

def posIdeleHom : {r : ℝ // 0 < r} →* IdeleGroup K where
  toFun s := posIdele s.1 s.2
  map_one' := by
    unfold posIdele
    refine Finset.prod_eq_one fun w _ => ?_
    convert map_one (moduleSection (K := K) w)
    exact one_pow _
  map_mul' s t := by
    unfold posIdele
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Positive.val_mul, mul_pow])

theorem posIdeleHom_apply (s : {r : ℝ // 0 < r}) : posIdeleHom K s = posIdele s.1 s.2 := rfl

theorem continuous_posIdeleHom : Continuous (posIdeleHom K) :=
  continuous_posIdele_subtype

variable (K n) in

def scalarUnits : IdeleGroup K →* AdelicGLn.AdelicGL K n :=
  (diagUnits n).comp
    { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem scalarUnits_apply (u : IdeleGroup K) : scalarUnits K n u = diagUnits n fun _ => u := rfl

theorem continuous_scalarUnits : Continuous (scalarUnits K n) :=
  (continuous_diagUnits n).comp (continuous_pi fun _ => continuous_id)

theorem scalarUnits_mul_comm (u : IdeleGroup K) (g : AdelicGLn.AdelicGL K n) :
    scalarUnits K n u * g = g * scalarUnits K n u := by
  refine Units.ext ?_
  simp only [Units.val_mul, scalarUnits_apply, coe_diagUnits]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable (K) in

def centralSection (n : ℕ) : {r : ℝ // 0 < r} →* AdelicGLn.AdelicGL K n :=
  (scalarUnits K n).comp ((posIdeleHom K).comp (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹))

theorem continuous_centralSection : Continuous (centralSection K n) :=
  continuous_scalarUnits.comp (continuous_posIdeleHom.comp (continuous_rpowHom _))

theorem centralSection_mul_comm (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    centralSection K n s * g = g * centralSection K n s :=
  scalarUnits_mul_comm _ g

variable (K n) in

def detModule : AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} :=
  (ideleModule K).comp (AdelicGLn.det K n)

theorem continuous_detModule : Continuous (detModule K n) :=
  continuous_ideleModule.comp (AdelicGLn.continuous_det K n)

theorem mem_normOneGL_iff_detModule {g : AdelicGLn.AdelicGL K n} :
    g ∈ normOneGL K n ↔ detModule K n g = 1 := by
  rw [mem_normOneGL]
  exact ⟨fun h => Subtype.ext (h.trans Positive.val_one.symm),
    fun h => (congrArg Subtype.val h).trans Positive.val_one⟩

theorem detModule_centralSection (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    detModule K n (centralSection K n s) = s := by
  refine Subtype.ext ?_
  have hd0 : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : (detModule K n (centralSection K n s) : ℝ) =
      ∏ _i : Fin n, (ideleModule K (posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s)) : ℝ) := by
    rw [detModule, MonoidHom.comp_apply, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply,
      scalarUnits_apply, det_diagUnits, map_prod, coe_finset_prod_pos]
  rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, posIdeleHom_apply,
    ideleModule_posIdele]
  change ((s.1 ^ ((n * Module.finrank ℚ K : ℝ))⁻¹) ^ Module.finrank ℚ K) ^ n = s.1
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le]
  have hne : (n * Module.finrank ℚ K : ℝ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hd0.ne')
  rw [show ((n * Module.finrank ℚ K : ℝ))⁻¹ * ((Module.finrank ℚ K * n : ℕ) : ℝ) = 1 by
    push_cast; field_simp, Real.rpow_one]

def glNormOneSplitting (hn : 0 < n) :
    AdelicGLn.AdelicGL K n ≃ₜ* normOneGL K n × {r : ℝ // 0 < r} :=
  GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
    continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm (normOneGL K n)
    (fun _ => mem_normOneGL_iff_detModule)

@[simp] theorem glNormOneSplitting_symm_apply (hn : 0 < n) (p : normOneGL K n × {r : ℝ // 0 < r}) :
    (glNormOneSplitting (K := K) hn).symm p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 := by
  rfl

theorem exists_measure_eq_mul_measure_image (hn : 0 < n)
    [SecondCountableTopology (AdelicGLn.AdelicGL K n)] [MeasurableSpace (AdelicGLn.AdelicGL K n)]
    [BorelSpace (AdelicGLn.AdelicGL K n)]
    (μ₁ : Measure (normOneGL K n)) [μ₁.IsHaarMeasure]
    (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ E : Set (normOneGL K n), MeasurableSet E →
      μ₁ E = c * μ ((fun p : normOneGL K n × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval)) := by
  have : SecondCountableTopology (normOneGL K n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set Φ : AdelicGLn.AdelicGL K n ≃ₜ* normOneGL K n × {r : ℝ // 0 < r} :=
    GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
      continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm
      (normOneGL K n) (fun _ => mem_normOneGL_iff_detModule) with hΦ
  have hΦs : ∀ p : normOneGL K n × {r : ℝ // 0 < r},
      Φ.symm p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 := fun p => rfl
  have hΦm : Measurable (Φ : AdelicGLn.AdelicGL K n → normOneGL K n × {r : ℝ // 0 < r}) :=
    Φ.continuous.measurable
  set lam : Measure (normOneGL K n × {r : ℝ // 0 < r}) := μ.map Φ with hlam
  have hlamH : lam.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hν : posRealMeasure posRealUnitInterval = 1 := posRealMeasure_posRealUnitInterval
  set ρ : Measure (normOneGL K n) :=
    Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ posRealUnitInterval)) with hρ
  have hρH : ρ.IsHaarMeasure := isHaarMeasure_map_fst_restrict lam posRealMeasure hν
  have hμ₁ : μ₁ = Measure.haarScalarFactor μ₁ ρ • ρ := Measure.isMulLeftInvariant_eq_smul μ₁ ρ
  refine ⟨(Measure.haarScalarFactor μ₁ ρ : ℝ≥0∞), ENNReal.coe_ne_top, fun E hE => ?_⟩
  have hS : MeasurableSet posRealUnitInterval := measurableSet_posRealUnitInterval
  have hρE : ρ E = μ (Φ ⁻¹' (E ×ˢ posRealUnitInterval)) := by
    rw [hρ, Measure.map_apply measurable_fst hE, Measure.restrict_apply (measurable_fst hE),
      hlam, Measure.map_apply hΦm]
    · congr 1
      ext p
      simp [and_comm]
    · exact (measurable_fst hE).inter (MeasurableSet.univ.prod hS)
  have himg : Φ ⁻¹' (E ×ˢ posRealUnitInterval) =
      (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval) := by
    ext g
    constructor
    · intro hg
      exact ⟨Φ g, hg, (hΦs (Φ g)).symm.trans (Φ.symm_apply_apply g)⟩
    · rintro ⟨p, hp, rfl⟩
      show Φ ((p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) ∈ E ×ˢ posRealUnitInterval
      rw [← hΦs p, ContinuousMulEquiv.apply_symm_apply]
      exact hp
  have h1 : μ₁ E = (Measure.haarScalarFactor μ₁ ρ • ρ) E :=
    congrArg (fun m : Measure (normOneGL K n) => m E) hμ₁
  rw [h1, Measure.smul_apply, hρE, himg, ENNReal.smul_def, smul_eq_mul]

end Reduction

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.Spherical
section
noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra HeckeAlgebraLevel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Characters

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem exists_ker_sphericalCharacter_eq (I : Ideal (SphericalHecke μ (F := F) (n := n)))
    [I.IsMaximal] : ∃ w : Fin n → ℂˣ,
      RingHom.ker (sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w)) = I := by
  haveI := isIntegral_satake (μ := μ) (F := F) (n := n)
  obtain ⟨w, hw⟩ := exists_ker_evalAt_comp_eq (satakeHom μ) satakeHom_injective I
  exact ⟨w, by rw [← evalAt_comp_satakeHom]; exact hw⟩

theorem exists_eq_sphericalCharacter (ω : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] ℂ) :
    ∃ χ : levi F n (id : Fin n → Fin n) →* ℂ, ∃ hχ : IsUnramified χ, ω = sphericalCharacter μ hχ := by
  have hsurj : Function.Surjective ω := fun c => ⟨algebraMap ℂ _ c, AlgHom.commutes ω c⟩
  haveI : (RingHom.ker ω).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) (RingHom.ker ω)
  refine ⟨unramifiedChar w, isUnramified_unramifiedChar w, AlgHom.ext fun h => ?_⟩
  have hmem : h - algebraMap ℂ _ (ω h) ∈ RingHom.ker ω := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  rw [← hw, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hmem
  exact hmem.symm

end Characters

theorem exists_subquotient_principalSeries {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ (integralGL F n) ≠ ⊥) :
    ∃ χ : levi F n (id : Fin n → Fin n) →* ℂ, IsUnramified χ ∧
      ∃ W : Subrepresentation (principalSeries F n χ),
        ∃ f : Representation.IntertwiningMap W.toRepresentation ρ, Function.Surjective f := by
  borelize (GL (Fin n) F)
  let μ : Measure (GL (Fin n) F) := Measure.haar
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  let s₀ := LinearMap.toSpanSingleton (SphericalHecke μ (F := F) (n := n))
    (fixedVectors ρ (integralGL F n)) ⟨v₀, hv₀⟩
  let I : Ideal (SphericalHecke μ (F := F) (n := n)) := LinearMap.ker s₀
  have hsimple := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  have hsurj : Function.Surjective s₀ :=
    ((isSimpleModule_iff_toSpanSingleton_surjective).1 hsimple).2 _
      fun h => h0 (congrArg Subtype.val h)
  haveI hI : I.IsMaximal := by
    rw [Ideal.isMaximal_def]
    exact isSimpleModule_iff_isCoatom.1 (IsSimpleModule.congr (LinearMap.quotKerEquivOfSurjective _ hsurj))
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) I
  set χ := unramifiedChar (F := F) w
  have hχ := isUnramified_unramifiedChar (F := F) w
  refine ⟨χ, hχ, ?_⟩
  set φ := sphericalVector hχ
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep χ)
  have hφK := sphericalVector_mem_fixedVectors hχ
  have hIv : ∀ h : SphericalHecke μ (F := F) (n := n), h ∈ I ↔
      heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0 := by
    intro h
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Subtype.ext_iff]
    rfl
  have hIφ : ∀ h : SphericalHecke μ (F := F) (n := n), h ∈ I ↔
      heckeAct μ (principalSeries F n χ) (h : HeckeAlgebra μ) φ = 0 := by
    intro h
    rw [heckeAct_sphericalVector hχ, smul_eq_zero, ← hw, RingHom.mem_ker, sphericalCharacter_apply]
    simp [φ, sphericalVector_ne_zero hχ]
  obtain ⟨A⟩ := nonempty_equiv_quotRep hKc hKo I hρ hv₀ h0 hIv
  let Φ : HeckeAlgebra μ →ₗ[ℂ] principalSeriesSpace F n χ := orbitMap φ (hs φ)
  have hΦ : ∀ f, Φ f = heckeAct μ (principalSeries F n χ) f φ := fun _ => rfl
  have hint : ∀ g f, Φ (leftReg μ g f) = principalSeries F n χ g (Φ f) := fun g f =>
    (heckeAct_ltrans g f.mem (hs φ)).symm
  have key : ∀ f g, heckeAct μ (principalSeries F n χ) (idem μ hKc hKo)
      (principalSeries F n χ g (Φ f)) =
        heckeAct μ (principalSeries F n χ) (cornerₗ hKc hKo (leftReg μ g f) : HeckeAlgebra μ) φ := by
    intro f g
    rw [hΦ, heckeAct_ltrans g f.mem (hs φ)]
    change heckeAct μ _ (idem μ hKc hKo) (heckeAct μ _ (leftReg μ g f : HeckeAlgebra μ) φ) = _
    rw [← heckeAct_mul _ _ (hs φ)]
    exact (heckeAct_corner hKc hKo hφK _).symm
  have hker : LinearMap.ker Φ ≤ heckeKernel hKc hKo I := by
    intro f hf g
    rw [LinearMap.mem_ker] at hf
    rw [hIφ, ← key, hf, map_zero]
    exact heckeAct_zero_right (idem μ hKc hKo).mem
  let W : Subrepresentation (principalSeries F n χ) :=
    ⟨LinearMap.range Φ, by
      rintro g _ ⟨f, rfl⟩
      exact ⟨leftReg μ g f, hint g f⟩⟩
  let Ψ : HeckeAlgebra μ →ₗ[ℂ] V := A.toLinearMap ∘ₗ (heckeKernel hKc hKo I).mkQ
  have hΨ : LinearMap.ker Φ ≤ LinearMap.ker Ψ := fun f hf => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (hker hf), map_zero]
  let T : LinearMap.range Φ →ₗ[ℂ] V :=
    (LinearMap.ker Φ).liftQ Ψ hΨ ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hT : ∀ f, T ⟨Φ f, LinearMap.mem_range_self Φ f⟩ = Ψ f := by
    intro f
    simp only [T, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hT' : ∀ (y : LinearMap.range Φ) (f) (_ : Φ f = y), T y = Ψ f := by
    rintro ⟨y, hy⟩ f rfl
    exact hT f
  refine ⟨W, ⟨T, fun g => LinearMap.ext fun y => ?_⟩, fun v => ?_⟩
  · obtain ⟨f, hf⟩ := y.2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    have hy : (W.toRepresentation g y : principalSeriesSpace F n χ) = Φ (leftReg μ g f) := by
      rw [hint, hf]
      rfl
    rw [hT' _ _ hy.symm, hT' y f hf]
    simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, Representation.Equiv.coe_toLinearMap]
    rw [← quotRep_mkQ]
    exact Representation.IntertwiningMap.isIntertwining _ _ A.toIntertwiningMap g _
  · obtain ⟨y, hy⟩ := A.toLinearEquiv.surjective v
    obtain ⟨f, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective y
    refine ⟨⟨Φ f, LinearMap.mem_range_self Φ f⟩, ?_⟩
    change T _ = v
    rw [hT]
    exact hy

end Spherical

end GroundTheory.Automorphic
end
end

