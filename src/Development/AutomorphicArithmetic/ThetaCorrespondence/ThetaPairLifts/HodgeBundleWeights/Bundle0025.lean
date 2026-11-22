import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3358
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionWeightBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3355
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0020
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryDivisorHasReducedEquation
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle
theorem exists_reduced_boundary_equation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  intro _ E _ _ _ H Dw l Xo c T Z hF _ y _
  have hsm := GlobalTheory.VarFlag.smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, -, hl⟩ :=
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  obtain ⟨h, hiso, hh, -, -⟩ := GlobalTheory.CompProport.exists_iso T Z B j hB hcov C f hπ hl
  have hmem : ∀ z : Y₀ T.X Z, h z ∉ CartierDiv.supp C.bd ↔ z ∈ U₀ T.X Z := fun z => by
    have e : GlobalTheory.Toroidal.genι T.Y (C.π (h z)) = T.X.π (inc₀ T.X Z z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    refine (not_congr (C.bd_supp (h z))).trans (not_not.trans ?_)
    change C.π (h z) ∈ Set.range T.Y.jQ ↔ T.X.π (inc₀ T.X Z z) ∈ Set.range T.Y.j
    refine exists_congr fun x => ?_
    rw [← e, Model.j, Scheme.Hom.comp_apply]
    exact (GlobalTheory.Toroidal.genι T.Y).isOpenEmbedding.injective.eq_iff.symm
  obtain ⟨V, hyV, t, ht, hrad⟩ := exists_section C.bd C.bd_eff C.bd_red (h y)
  have hg : ∀ z (hz : z ∈ h ⁻¹ᵁ V), ger z hz (h.app V t) = (h.stalkMap z).hom (ger (h z) hz t) :=
    fun z hz => (Scheme.Hom.germ_stalkMap_apply h V z hz t).symm
  have hu : ∀ z (hz : z ∈ h ⁻¹ᵁ V), IsUnit (ger z hz (h.app V t)) ↔ z ∈ U₀ T.X Z := fun z hz => by
    rw [hg, isUnit_map_iff]
    exact (ht (h z) hz).trans (hmem z)
  refine ⟨h ⁻¹ᵁ V, hyV, h.app V t, hu, fun W hW s hs z hz => ?_⟩
  obtain ⟨n, c', hc⟩ := dvd_pow_of_vanishing _ _ _ hu W hW s hs z hz
  have hb := GlobalTheory.BoundaryDivisor.stalkMap_bijective h z
  obtain ⟨b, hb'⟩ := hb.2 (ger z hz s)
  obtain ⟨c'', rfl⟩ := hb.2 c'
  rw [hg, ← hb', ← map_pow, ← map_mul] at hc
  rw [hg, ← hb']
  exact map_dvd _ (hrad _ _ b n ⟨c'', hb.1 hc⟩)
end GlobalTheory.BdEquation
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_divisor_has_reduced_equation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  first | exact @_root_.GlobalTheory.BdEquation.exists_reduced_boundary_equation | exact _root_.GlobalTheory.BdEquation.exists_reduced_boundary_equation | (intros; apply _root_.GlobalTheory.BdEquation.exists_reduced_boundary_equation <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNonzeroSectionWeightBound
section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSteep
section Tau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end Tau
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.ThetaConst GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.AllWt in
theorem exists_theta_multiplication_rule (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hM : 5 ^ 4 ∣ l.M)
    (Z : Comp Xo c) (s : ∀ τ, FlatSec U x Z τ) :
    ∃ f : secZ Xo c (exOf Dw ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw) 0), f.1 ∈ suppOn Z ∧ f ≠ 0 ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), (∀ a, io a ∈ (algebraMap T.V T.Fr).range) →
        (letI := io.toAlgebra; LiesOn Z y.1) → GlobalTheory.SlopeRec.HasPhi y φ → evI y f.1 ≠ 0 →
          8 * φ / 625 ≤ (vV T.V (evI y f.1) : ℝ) := by
  obtain ⟨K, hK, hKv⟩ := exists_key Xo c hL.pos hL.good
  have h : HasPts U Z := hasPts U hL.pos hL.good hL.unf Z
  have h5 : Odd 5 := by decide
  obtain ⟨x₀, hx₀⟩ := exists_isAdm Dw (R := 5) (by norm_num)
  obtain ⟨u, f, hf, hfZ⟩ := exists_isGenRule_nonzeroOn (Xo := Xo) (c := c) h5 (by norm_num) hM x₀ Z
  refine ⟨⟨thetaOn h s K f, thetaOn_mem_secZ h s hK (IsTauRule.mem_sec h5 hf)⟩, thetaOn_mem_suppOn h s K f,
    fun h0 => ((nonzeroOn_thetaOn_iff h s K f).2 hfZ).ne_zero (congrArg Subtype.val h0), fun T io y φ hio hZ hφ hne => ?_⟩
  letI := io.toAlgebra
  have hid : evI y (idem Z) = 1 := evR_idem hZ y.2.1
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hio0 : ∀ a, a ≠ 0 → vV T.V (io a) = 0 := fun a ha => by
    have h1 := (mem_range_iff T _).1 (hio a)
    have h2 := (mem_range_iff T _).1 (hio a⁻¹)
    have h3 := vV_mul (V := T.V) ((map_ne_zero io).2 ha) ((map_ne_zero io).2 (inv_ne_zero ha))
    rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    omega
  have hs : ∀ τ, ev (s τ).sig ∈ (algebraMap T.V T.Fr).range := fun τ => by
    have h1 := _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws hP hP.q2 E H Dw l Xo c r U x hL Z τ (ArchSec.ofConst (s τ)) T io y hio0 hZ
    change nval T.V 1 (ev (s τ).sig) = 0 at h1
    by_cases h0 : ev (s τ).sig = 0
    · exact h0 ▸ zero_mem _
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_eq_zero, Int.cast_eq_zero] at h1
    exact (mem_range_iff T _).2 h1.ge
  have e : evI y (thetaOn h s K f) = evI y f ^ 8 * (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    change ev _ = ev f ^ 8 * _
    rw [thetaOn, shift_sig]
    simp only [map_mul, map_pow, map_prod]
    rw [show ev (idem Z) = 1 from hid, one_mul, mul_assoc]
  have hB : ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q)) ∈ (algebraMap T.V T.Fr).range :=
    mul_mem (pow_mem (hKv T io y hio) _) (prod_mem fun τ _ => pow_mem (hs τ) _)
  change evI y (thetaOn h s K f) ≠ 0 at hne
  change _ ≤ (vV T.V (evI y (thetaOn h s K f)) : ℝ)
  rw [e] at hne ⊢
  have hf0 : evI y f ≠ 0 := fun h0 => hne (by rw [h0]; simp)
  have b1 := tau_bound y hφ h5 (by norm_num) (fun _ => hx₀.spans (by norm_num) u) hf hf0
  have b2 : (0 : ℝ) ≤ vV T.V (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    exact_mod_cast (mem_range_iff T _).1 hB
  rw [vV_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne),
    show vV T.V (evI y f ^ 8) = 8 * vV T.V (evI y f) by simp [vV]]
  push_cast at b1 ⊢
  linarith
variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
variable {X} in
set_option maxHeartbeats 1000000 in
theorem exists_section_of_theta_datum (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : FlatCore.Laws U x)
    (hM : 5 ^ 4 ∣ l.M) (TF : TorFlag Xo c) (s : ∀ τ, FlatLine.FlatSec U x Z τ)
    (hdeg : ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ) :
    ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw)) ⊤, θ ≠ 0 ∧
      ∀ (y : Y₀ TF.X Z) ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ j hj (m : ℤ),
        ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          8 * φ / 625 ≤ (m : ℝ) := by
  obtain ⟨f, hfZ, hf0, hf⟩ := _root_.GlobalTheory.ThetaSteep.exists_theta_multiplication_rule hP hL hM Z s
  obtain ⟨hs, -, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hL.geo
  haveI := hs
  haveI := hc
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (FlagTan.dimFlag Dw) _
  haveI := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  have hN : Geo.Tor.IsNormalScheme (Y₀ TF.X Z) := fun y => by
    obtain ⟨_, _⟩ := TF.X.normal (inc₀ TF.X Z y)
    let e := (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  obtain ⟨θ, hθ⟩ := exists_extension hN (isLB_L₀ TF.X Z _) (dense_U₀ TF.X Z).nonempty (sec₀ TF.X Z _ f)
    fun y hy _ j hj => by
      obtain ⟨ν, hν⟩ := exists_centred y
      obtain ⟨_, -, T, io, y', g, ρ, φT, hρ, hφT, -, hpt, hval⟩ := hdeg y hy ν hν
      obtain ⟨g1, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
      refine ⟨T, g, g1, g2, fun hO hi => ?_⟩
      obtain ⟨a1, a2, -, a4⟩ := through_point TF.X Z y T io y' g hpt
      obtain ⟨u, hu⟩ := a4 _ f j hj hO hi
      rw [hu]
      refine mul_mem ⟨_, rfl⟩ ?_
      by_cases h0 : evI y' f.1 = 0
      · exact h0 ▸ zero_mem _
      have b1 := hf T io y' φT a1 a2 hφT h0
      have b2 := hφT.nonneg
      refine (mem_range_iff T _).2 ?_
      have : (0 : ℝ) ≤ vV T.V (evI y' f.1) := by linarith
      exact_mod_cast this
  refine ⟨θ, fun h0 => hf0 (eq_zero_of_sec₀ TF.X Z hfZ (by rw [← hθ, h0, map_zero])), fun y ν hν φ hφ j hj m hm => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  obtain ⟨-, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
  obtain ⟨a1, a2, a3, a4⟩ := through_point TF.X Z y T io y' g hpt
  have hi := top_le_stalkPt y ((algebraMap T.V T.Fr).comp g) _ hj
  obtain ⟨u, hu⟩ := a4 _ f j hj a3 hi
  rw [← hθ, val_restr_pt le_top _ j (top_le_stalkPt y _ ⊤ (memTop y)), val_stalkPt y j (memTop y) hj,
    RingHom.comp_apply] at hu
  have hne : ν (H0.germ j y (memTop y) hj θ) ≠ 0 := hm ▸ WithZero.coe_ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j y (memTop y) hj θ)) ≠ 0 := fun h => hne (by
    rw [(injective_iff_map_eq_zero _).1 g2 _ ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective T.V T.Fr) _ h),
      map_zero])
  have hv := hval _ hne
  rw [hu] at hg0 hv
  rw [hm, vV_mul (left_ne_zero_of_mul hg0) (right_ne_zero_of_mul hg0), vV_unit, zero_add,
    show WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m from rfl] at hv
  have b1 := mul_le_mul_of_nonneg_left (hf T io y' φT a1 a2 hφT (right_ne_zero_of_mul hg0)) hρ.le
  push_cast at hv
  linarith
end Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_theta_section_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  intro h1 h2 h3 h4
  refine (((_root_.GlobalTheory.T.exists_pos_phi_at_centred_point h1 h2 h3 h4).and h4).and (GlobalTheory.CovTop.Sizes.hostN 0)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C, hC, x0, hx0⟩, ⟨C₁, -, x1, hx1⟩⟩, ⟨C₂, -, x2, hx2⟩⟩ := h
  refine ⟨C, hC, max x0 (max x1 x2), fun x hx hle ι p hp i hi Y hY Z TF => ?_⟩
  have l0 : x0 ≤ x := (le_max_left _ _).trans hle
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hdeg := hx0 x hx l0 ι p hp i hi Y hY Z TF
  have hfl := hx1 x hx l1 ι p hp i hi Y hY
  have hnum := hx2 x hx l2 ι p hp i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact Dvd.dvd.mul_left ((pow_dvd_pow_of_dvd (by norm_num) 4).trans (pow_dvd_pow 15 (four_le_expL hnum.big.2.1))) _
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have := hnum.f8
    have := hnum.deg
    omega
  obtain ⟨θ, hθ, hb⟩ := _root_.GlobalTheory.ThetaSteep.exists_section_of_theta_datum Z h1 hL hM TF (fun τ => (hfl Z τ).1.some) hdeg
  exact ⟨θ, hθ, fun la _ f hf' => vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF la
    (mul_mem_vanBd TF.X Z _ θ ((GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _).space_le hf')),
    fun y _ ν hν φ hφ j hj m hm => hb y ν hν φ hφ j hj m hm⟩
end GlobalTheory.ThetaSteep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  first | exact @_root_.GlobalTheory.ThetaSteep.exists_theta_section_alt | exact _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt | (intros; apply _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulMemCuspFormsOfWeightMatch
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.WtMatchBar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 800000 in
theorem exists_pow_mul_mem_cuspForms_of_weight_match : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  intro hP D T j Y e o hY hE hp hq la hla hbar f hf
  obtain ⟨u, u', t₁, hu, ht₁, huu, hu'⟩ := _root_.GlobalTheory.T.inverse_invariant_integral hP D T j Y e o hY hE
  obtain ⟨N, hN, hU2⟩ := _root_.GlobalTheory.T.detLine_flat_unit_exists hP D T j Y e o hY hE
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp hP D T j Y e o hY hE la f hf (u ^ M) (u' ^ M) (t₁ ^ M) _ (pow_mem_secZ hu M)
    (pow_ne_zero _ ht₁) (by rw [← mul_pow, huu, smul_pow, one_pow])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max K (2 * M + N) := ⟨_, rfl⟩
  obtain ⟨w, a, hDom, hex⟩ := GlobalTheory.T.exists_dominant_exponents_matching_weight_bar_gap _ _ _ la hp hq hla hbar N M k hN (by omega)
  obtain ⟨φ, φ', t₂, hφ, ht₂, hφφ, hφ', hφb⟩ := hU2 w
  refine ⟨k, a, 2 * M, u ^ M * φ, u' ^ M * φ', t₁ ^ M * t₂, hDom, by omega, ?_, mul_ne_zero (pow_ne_zero _ ht₁) ht₂, ?_, ?_⟩
  · refine hK k (hk ▸ le_max_left _ _) φ φ' t₂ _ hφ ht₂ hφφ hφb a (2 * M) hDom ?_
    rw [← GlobalTheory.AllWt.secZ_nat, hex]
    have h1 : f ^ (k + 1) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ ((k + 1) • GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) :=
      pow_mem_secZ (GlobalTheory.AllWt.cuspW_le_secZ _ hf) (k + 1)
    have h2 := GlobalTheory.AllWt.mul_mem_secZ h1 (GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ hu M) hφ)
    convert h2 using 2
    rw [nsmul_exOf_zero_one, ← GlobalTheory.AllWt.exOf_add, zero_add, add_zero]
  · rw [mul_mul_mul_comm, ← mul_pow, huu, hφφ, smul_pow, one_pow, smul_mul_smul_comm, one_mul]
  · intro la' v hv
    have hV := isVal_valSet la' v hv
    rw [hV.mul]
    rw [hM]
    exact add_nonneg (val_pow_succ_nonneg hV (hu' la' v hv) _) (hφ' la' v hv)
end GlobalTheory.WtMatchBar
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  first | exact @_root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | exact _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | (intros; apply _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match <;> assumption)
end
end

