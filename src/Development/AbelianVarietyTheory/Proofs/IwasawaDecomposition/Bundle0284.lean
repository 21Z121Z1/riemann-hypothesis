import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrEqUnique

theorem eq_one_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} (h : ChrEq c 1) (x : (AE D)ˣ) : c x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D c h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) c 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

noncomputable def phase : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)])⟩
  map_one' := Circle.ext (by
    change ((1 : ℂˣ) : ℂ) / ((‖((1 : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = 1
    simp)
  map_mul' x y := Circle.ext (by
    change ((x * y : ℂˣ) : ℂ) / ((‖((x * y : ℂˣ) : ℂ)‖ : ℝ) : ℂ) =
      (x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ) * ((y : ℂ) / ((‖(y : ℂ)‖ : ℝ) : ℂ))
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])

theorem continuous_phase : Continuous phase :=
  Continuous.subtype_mk (Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)) _

noncomputable def normPow (t : ℝ) : ℂˣ →* Circle where
  toFun z := Circle.exp (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      Circle.exp_add]

theorem continuous_normPow (t : ℝ) : Continuous (normPow t) :=
  Circle.exp.continuous.comp (continuous_const.mul
    (Units.continuous_val.norm.log fun z => norm_ne_zero_iff.2 z.ne_zero))

theorem eq_one_of_forall {z : ℂˣ} (h : ∀ φ : ℂˣ →* Circle, Continuous φ → φ z = 1) : z = 1 := by
  have hn : ‖(z : ℂ)‖ = 1 := by
    by_contra hne
    have hl : Real.log ‖(z : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 z.ne_zero) hne
    have h1 := h _ (continuous_normPow (Real.pi / Real.log ‖(z : ℂ)‖))
    change Circle.exp (_ * _) = 1 at h1
    rw [div_mul_cancel₀ _ hl] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp only [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h2
    norm_num at h2
  have h2 := congrArg (fun w : Circle => (w : ℂ)) (h _ continuous_phase)
  change (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 at h2
  rw [hn, Complex.ofReal_one, div_one] at h2
  exact Units.ext h2

theorem hchar_eq_one (D : D7) (ξ : HChar D.host.E) (h : ∀ P k, ξ.locK P k = 1) : ξ = 1 := by
  obtain ⟨Φ, hΦ, -, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Φ.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  refine Subtype.ext (MonoidHom.ext fun y => eq_one_of_forall fun φ hφ => ?_)
  have hc : ChrEq (φ.comp (ξ.1.comp u)) (1 : HChar D.host.E) := by
    refine ⟨⟨hφ.comp (ξ.2.1.comp hu), fun k => ?_⟩, fun P e he k x hx => ?_⟩
    · have : u (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (h1 k)
      change φ (ξ.1 (u _)) = 1
      rw [this, ξ.2.2, map_one]
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Φ (x : AE D) = _
        rw [hx, h2 P e he]
      have h3 : ξ.1 (localIdele D.host.E P (atFin P k)) = 1 := h P k
      change ((φ (ξ.1 (u x)) : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [this, h3, map_one]
      rfl
  have hy : u (Units.map Φ.symm.toRingHom.toMonoidHom y) = y := Units.ext (Φ.apply_symm_apply _)
  have := eq_one_of_chrEq hc (Units.map Φ.symm.toRingHom.toMonoidHom y)
  change φ (ξ.1 (u _)) = 1 at this
  rwa [hy] at this

theorem hchar_unique (D : D7) (c : IdC D) (χ χ' : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c χ') : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine hchar_eq_one D _ fun P k => ?_
  obtain ⟨Φ, -, -, -, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := PlaceIdem.exists_isPlIdem D j j1 j2 j3 P
  let x : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (localIdele D.host.E P (atFin P k))
  have hx : (x : AE D) = locE D e (k : D.host.E) := Φ.symm_apply_eq.2 (h2 P e he k).symm
  change χ.locK P k * (χ'.locK P k)⁻¹ = 1
  rw [mul_inv_eq_one]
  exact Units.ext ((h.2 P e he k x hx).symm.trans (h'.2 P e he k x hx))

theorem idc_unique (D : D7) (c c' : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c' χ) : c = c' := by
  have hc : ChrEq (c * c'⁻¹ : (AE D)ˣ →* Circle) (1 : HChar D.host.E) := by
    refine ⟨⟨h.1.1.mul h'.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.1.2, h'.1.2, inv_one, one_mul]
    · change ((c x * (c' x)⁻¹ : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, h.2 P e he k x hx, h'.2 P e he k x hx, mul_inv_cancel₀ (Units.ne_zero _)]
      rfl
  exact MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_chrEq hc x)

theorem isUnitary_of_chrEq (D : D7) (c : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) : χ.IsUnitary := by
  have hc := h.1
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (hc.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨hc, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [hchar_unique D c χ χ' h h']
  exact fun x => Circle.norm_coe (c (u x))

theorem chrEq_unique : ∀ (D : D7), (∀ (c : IdC D) (χ χ' : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c χ' → χ = χ') ∧ (∀ (c c' : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c' χ → c = c') ∧ ∀ (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → χ.IsUnitary :=
  fun D => ⟨hchar_unique D, idc_unique D, isUnitary_of_chrEq D⟩

end GlobalTheory.ChrEqUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.Lv

section Build
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp [reL, reV, LinearEquiv.funCongrLeft, LinearMap.funLeft]

theorem reGL_rfl_map {a : ℕ} {R : Type} [CommRing R] (U : Subgroup (GL (Fin a) R)) :
    U.map (reGL (rfl : a = a) R).toMonoidHom = U := by
  have : ∀ x, reGL (rfl : a = a) R x = x := fun x => by
    ext i j
    simp [reGL]
  ext x
  simp [Subgroup.mem_map, this]

theorem exists_herm_level (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (gp : Fin 2 → ℕ) (T f : ℕ)
    {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (K : StepLevel F E hc.sig J T f bad)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), (gp 0 : 𝓞 F) ∉ v.asIdeal → (gp 1 : 𝓞 F) ∉ v.asIdeal → v ∉ bad)
    (hg : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → ∀ x ∈ levelVL hc.sig J v K.Lb,
      (∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z) → x ∈ K.Uloc v)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ K.Uloc v ↔ x ∈ levelVL hc.sig J v K.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J K.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb) :
    ∃ L : Formalism.L2.Herm.StepLevel hc S gp T f, K.Lb = reL h L.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  have hJ' : J = S.gram := by rw [hJ]; ext a b; simp
  subst hJ'
  clear hJ
  refine ⟨{ Lb := K.Lb, Lb_fin := K.Lb_fin, Lb_span := K.Lb_span, Lb_int := fun x hx => Submodule.subset_span (K.Lb_int x hx),
            Lb_dual := ?_, Lb_index := K.Lb_index, Uloc := K.Uloc, Uloc_lev := K.Uloc_lev, Uloc_hyp := ?_, Uloc_g := ?_, UlocAlt := ?_,
            U := K.U, U_eq := K.U_eq }, ?_, ?_, ?_⟩
  · intro y hy
    unfold Formalism.L2.Herm.dualL at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact K.Lb_dual y hy
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul s a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  · intro v h0 h1 h2
    exact K.Uloc_hyp v (hbad v h0 h1) h2
  · intro a v h x hx
    exact hg a v h x hx.1 hx.2
  · intro v h x
    exact hT v h x
  · exact (reL_rfl _).symm
  · intro v; exact (reGL_rfl_map _).symm
  · exact (reGL_rfl_map _).symm

end Build
end GlobalTheory.Mem.Col2.Lv

namespace GlobalTheory.Mem.Col2.Lv
section W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uloc_T_iff (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (p q : 𝓞 E) (hq : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T.Prime) (hL : S.Lb = rll_dLat n ((p : E)⁻¹))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hunif : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    x ∈ S.Uloc v ↔ x ∈ levelVL σ J v S.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  subst hJ
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hp0 : (p : E) ≠ 0 := fun h => hT0 (by rw [← hpq, h, zero_mul])
  refine ⟨fun hx => ⟨S.Uloc_lev v hx, GlobalTheory.T.level_acts_trivially_on_discriminant_group σ hσ S p q hq hpq hT.ne_zero hL ?_ v hv ?_ x hx⟩, fun h => GlobalTheory.uloc_of_triv_disc σ S v hv x h.1 h.2⟩
  · rw [hL]; exact GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq
  · intro m hm d c hd hc
    exact GlobalTheory.T.unitaryScalar_eq_one_mod_of_fixes_simple_module σ hdeg hσ hfix hun v T hT hunif (S.fM v hv) (S.fM_card v hv) m hm d c hd hc

end W

theorem baseL_eq (B : Base) (n : ℕ) [NeZero n] (t : 𝓞 B.host.E) (ht : (t : B.host.E) ≠ 0) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (h : ∀ x, x ∈ L ↔ x ∈ baseL B n t) : L = rll_dLat n ((t : B.host.E)⁻¹) := by
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = lastIdx n := by
    intro j
    have := NeZero.pos n
    constructor
    · intro e; apply Fin.ext; simp [lastIdx]; omega
    · intro e; rw [e]; simp [lastIdx]; omega
  ext x
  rw [h, rll_mem_dLat]
  constructor
  · intro hx
    refine ⟨fun i _ => ?_, ?_⟩
    · obtain ⟨r, e, -⟩ := hx i
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e, hd⟩ := hx (lastIdx n)
      obtain ⟨c, rfl⟩ := hd ((hlast _).2 rfl)
      refine ⟨c, ?_⟩
      rw [e]
      show _ = _ * algebraMap (𝓞 B.host.E) B.host.E (t * c)
      rw [map_mul]
      exact (inv_mul_cancel_left₀ ht _).symm
  · rintro ⟨h1, c, hc⟩ j
    by_cases hj : j = lastIdx n
    · subst hj
      refine ⟨t * c, ?_, fun _ => dvd_mul_right _ _⟩
      have e : x (lastIdx n) = (t : B.host.E) * (c : B.host.E) := by
        have : algebraMap (𝓞 B.host.E) B.host.E c = (t : B.host.E)⁻¹ * x (lastIdx n) := hc
        show _ = _
        rw [show (c : B.host.E) = algebraMap (𝓞 B.host.E) B.host.E c from rfl, this, mul_inv_cancel_left₀ ht]
      rw [e]; rfl
    · obtain ⟨r, hr⟩ := h1 j hj
      exact ⟨r, hr.symm, fun e => absurd ((hlast j).1 e) hj⟩

end GlobalTheory.Mem.Col2.Lv

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Mem.Col2.TC.level_of_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch chOf F hF i hi cl stab _ lat K Hs lam hG hLb
  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  haveI : NeZero ((I.rec7 l Z).R.N i) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : K.lev.Lb = rll_dLat ((I.rec7 l Z).R.N i) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 K.lev.Lb ?_
    rw [hF.piU]; exact hLb
  refine GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (I.rec7 l Z).host.g _ _ rfl K.lev ?_ ?_ ?_
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ K.lev F.gl hG a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram K.lev F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v h) x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem iSup_range_weight_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  intro E _ _ _ n π τ lam h
  obtain ⟨-, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.exists_embRet E n τ
  have heq : (GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  have hσ : Representation.IsIrreducible ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
    rw [heq]
    exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)
  let F : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype))
      (π.rep.comp (embU n τ).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h0 =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))
  exact (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (embU n τ) π.V _ _ π.rep (embU n τ).subtype _ _
    π.isIrreducible_rep hσ hσ (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
section
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000

theorem inner_eq_of_norm_sq {K V E M : Type} [Field K] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup M] [Module K M] (σ : K →+* ℂ) (j : M →ₛₗ[σ] V) (hspan : Submodule.span ℂ (Set.range j) = ⊤) (k : K)
    (hk : (σ k).im ≠ 0) (e : V →ₗ[ℂ] E) (q : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : ∀ m, ((‖e (j m)‖ ^ 2 : ℝ) : ℂ) = q (j m) (j m))
    (y y' : V) : inner ℂ (e y) (e y') = q y y' := by
  let D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun y y' => inner ℂ (e y) (e y') - q y y')
    (fun y z y' => by simp only [map_add, inner_add_left, LinearMap.add_apply]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_left, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun y y' z => by simp only [map_add, inner_add_right]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring)
  have hDapp : ∀ y y', D y y' = inner ℂ (e y) (e y') - q y y' := fun y y' => rfl
  have h0 : ∀ m, D (j m) (j m) = 0 := by
    intro m
    rw [hDapp, ← hn m, inner_self_eq_norm_sq_to_K]
    simp
  have hsym : ∀ m m', D (j m) (j m') + D (j m') (j m) = 0 := by
    intro m m'
    have h := h0 (m + m')
    simp only [map_add, LinearMap.add_apply, h0 m, h0 m'] at h
    linear_combination h
  have hpair : ∀ m m', D (j m) (j m') = 0 := by
    intro m m'
    have h1 := hsym m (k • m')
    rw [j.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
    have h2 := hsym m m'
    have h3 : (σ k - starRingEnd ℂ (σ k)) * D (j m) (j m') = 0 := by linear_combination h1 - starRingEnd ℂ (σ k) * h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exfalso
      rw [Complex.sub_conj] at h4
      simp [hk] at h4
    · exact h4
  have h1 : ∀ m, D (j m) = 0 := fun m => LinearMap.ext_on_range hspan fun m' => by rw [hpair m m']; rfl
  have hall : D = 0 := LinearMap.ext_on_range hspan fun m => by rw [h1 m]; rfl
  have h := congrArg (fun D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => D y y') hall
  simp only [hDapp, LinearMap.zero_apply] at h
  exact sub_eq_zero.1 h

theorem exists_embLL_im_ne {B : Base} (hX : B.fields.Ok) : ∃ k : B.LL, (B.embLL k).im ≠ 0 := by
  have hc : (InfinitePlace.mk (B.embLL : B.fields.K →+* ℂ)).IsComplex := hX.cplxK.isComplex _
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  by_contra hne
  push_neg at hne
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hne x)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def cjPol (ι : Type) (n : ℕ) : Pol ℂ ι n →ₗ⋆[ℂ] Pol ℂ ι n where
  toFun p := MvPolynomial.map (starRingEnd ℂ) p
  map_add' p q := map_add _ p q
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, RingHom.id_apply]

theorem map_conj_smul {ι : Type} {n : ℕ} (r : ℂ) (p : Pol ℂ ι n) :
    MvPolynomial.map (starRingEnd ℂ) (r • p) = starRingEnd ℂ r • MvPolynomial.map (starRingEnd ℂ) p :=
  (cjPol ι n).map_smulₛₗ r p

abbrev rowS (a : I.ι) : GSD B.fields.K := mtildeGSD (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps

theorem rowS_ok (hX : B.fields.Ok) (a : I.ι) : (rowS I a).Ok :=
  mtildeOk (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) hX I.Ps

def cTerm (a : I.ι) (c : (rowS I a).Cl) (F G : MtCx I a) : ℂ :=
  ((Nat.card (@MulAction.stabilizer (rowS I a).G (rowS I a).D _ (rowS I a).actD ((rowS I a).outSec.rep c)) : ℕ) : ℂ)⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 ((rowS I a).outSec.rep c))) (G.1 ((rowS I a).outSec.rep c))

theorem cTerm_add_left (a : I.ι) (c : (rowS I a).Cl) (F F' G : MtCx I a) :
    cTerm I a c (F + F') G = cTerm I a c F G + cTerm I a c F' G := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply, mul_add]

theorem cTerm_smul_left (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c (r • F) G = starRingEnd ℂ r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_conj_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem cTerm_add_right (a : I.ι) (c : (rowS I a).Cl) (F G G' : MtCx I a) :
    cTerm I a c F (G + G') = cTerm I a c F G + cTerm I a c F G' := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add, mul_add]

theorem cTerm_smul_right (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c F (r • G) = r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_smul, smul_eq_mul]
  ring

def cSum (hX : B.fields.Ok) (a : I.ι) : MtCx I a →ₗ⋆[ℂ] MtCx I a →ₗ[ℂ] ℂ :=
  letI := (rowS_ok I hX a).fintypeCl
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun F G => ∑ c : (rowS I a).Cl, cTerm I a c F G)
    (fun F F' G => by simp only [cTerm_add_left, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_left, Finset.mul_sum, smul_eq_mul])
    (fun F G G' => by simp only [cTerm_add_right, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])

theorem cSum_apply (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) :
    cSum I hX a F G = letI := (rowS_ok I hX a).fintypeCl; ∑ c : (rowS I a).Cl, cTerm I a c F G := rfl

end GlobalTheory.Mem.Df

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
section
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

def domGram (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 - Matrix.of x * (Matrix.of x)ᴴ)⁻¹)ᵀ

def IsNegSq {E : Type*} [AddCommGroup E] [Module ℂ E] {m : ℕ} (F : E → E → Matrix (Fin m) (Fin m) ℂ) (r : ℕ) : Prop :=
  ∃ (S : Matrix (Fin m) (Fin m) ℂ) (T : E →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det ∧
    ∀ ξ η, F ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S

def sqPoly {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C ((T (coordVec a) * (T (coordVec b))ᴴ) i j) * X (a, b)

end GlobalTheory.PointFormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), IsAutFunSm θ V (rTr V (atTau θ V τ g) φ) := by
  first | exact @GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | (intros; apply GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau <;> assumption)
end

