import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsPrincipalCongruenceLevelInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem mat_nhds {R : Type} [TopologicalSpace R] [AddGroup R] [IsTopologicalAddGroup R]
    (t : Set (Matrix (Fin 2) (Fin 2) R)) (c : Matrix (Fin 2) (Fin 2) R) (ht : t ∈ 𝓝 c) :
    ∃ W ∈ 𝓝 (0 : R), ∀ m : Matrix (Fin 2) (Fin 2) R, (∀ i j, m i j - c i j ∈ W) → m ∈ t := by
  have hc : ContinuousAt (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) 0 := by
    refine Continuous.continuousAt ?_
    refine continuous_matrix fun i j => ?_
    exact ((continuous_apply j).comp (continuous_apply i)).add continuous_const
  have h0 : (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t ∈ 𝓝 (0 : Fin 2 → Fin 2 → R) :=
    hc.preimage_mem_nhds (by
      have : (Matrix.of fun i j => (0 : Fin 2 → Fin 2 → R) i j + c i j : Matrix (Fin 2) (Fin 2) R) = c := by
        ext i j; simp
      rw [this]; exact ht)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t1, ht1, hI⟩ := h0
  have ht2 : ∀ i, ∃ W ∈ 𝓝 (0 : R), ∀ m : Fin 2 → R, (∀ j, m j ∈ W) → m ∈ t1 i := fun i => by
    have h := ht1 i
    rw [Pi.zero_apply, nhds_pi, Filter.mem_pi] at h
    obtain ⟨J, -, s, hs, hJ⟩ := h
    exact ⟨⋂ j, s j, Filter.iInter_mem.2 hs, fun m hm => hJ fun j _ => Set.mem_iInter.1 (hm j) j⟩
  choose W hW hWt using ht2
  refine ⟨⋂ i, W i, Filter.iInter_mem.2 hW, fun m hm => ?_⟩
  have : (fun i j => m i j - c i j) ∈ (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t :=
    hI fun i _ => hWt i _ fun j => Set.mem_iInter.1 (hm i j) i
  have e : (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) = m := by
    ext i j; simp
  change (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) ∈ t at this
  rwa [e] at this

private theorem gl_nhds {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (V : Set (GL (Fin 2) R)) (hV : V ∈ 𝓝 (1 : GL (Fin 2) R)) :
    ∃ W ∈ 𝓝 (0 : R), ∀ k : GL (Fin 2) R, (∀ i j, k.val i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ W) →
      (∀ i j, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ W) → k ∈ V := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨t, ht, hts⟩ := hV
  rw [map_one] at ht
  have ht' : t ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) R), MulOpposite.op (1 : Matrix (Fin 2) (Fin 2) R)) := ht
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 ht'
  have hw' : MulOpposite.op ⁻¹' w ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) R) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hw
  obtain ⟨W1, hW1, h1⟩ := mat_nhds u 1 hu
  obtain ⟨W2, hW2, h2⟩ := mat_nhds _ 1 hw'
  refine ⟨W1 ∩ W2, Filter.inter_mem hW1 hW2, fun k hk hk' => hts ?_⟩
  exact huw (Set.mk_mem_prod (h1 _ fun i j => (hk i j).1) (h2 _ fun i j => (hk' i j).2))

private theorem pInf_zero {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : A E) (hx : x.1 = 0) : pInf E x = 0 := by
  change (infEq E).symm x.1 = 0
  rw [hx, map_zero]

theorem UpperTheory.exists_principalCongruence_level_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (f : Sm E 2), f ∈ P.V → ∀ h : GL (Fin 2) (A E), ∃ M : ℕ, 0 < M ∧ ∀ κ : GL (Fin 2) (A E), CongE M κ → ∀ g, f.1 (g * κ * h) = f.1 (g * h) := by
  intro E _ _ _ P f hf h
  have hopen : IsOpen {k | GlobalTheory.CuspRep.finRep E 2 k f = f} := (P.cusp f hf).1.level
  obtain ⟨l, hl⟩ : ∃ l, l = GeneralLinearGroup.map (pFin E) h := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = GeneralLinearGroup.map (pInf E) h := ⟨_, rfl⟩
  have hh : h = infGL E 2 y * finGL E 2 l := by rw [hy, hl]; exact (infGL_mul_finGL h).symm
  have hc : Continuous fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hV : (fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l) ⁻¹' {k | GlobalTheory.CuspRep.finRep E 2 k f = f} ∈ 𝓝 (1 : GL (Fin 2) (Af E)) :=
    hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp))
  obtain ⟨W, hW, hWk⟩ := gl_nhds _ hV
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hM : 0 < Ideal.absNorm (Ideal.span {d}) := by
    refine Nat.pos_of_ne_zero fun h0 => hd0 ?_
    rw [Ideal.absNorm_eq_zero_iff] at h0
    simpa using h0
  refine ⟨Ideal.absNorm (Ideal.span {d}), hM, fun κ hκ g => ?_⟩
  have hent : ∀ x : A E, ∀ c ∈ Oh E, x = (Ideal.absNorm (Ideal.span {d}) : A E) * c → pFin E x ∈ W := by
    rintro x c ⟨-, hc2⟩ rfl
    have hint : algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2 ∈ integralFiniteAdeles (𝓞 E) E := by
      rw [mem_integralFiniteAdeles]
      intro v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) v * c.2 v) ≤ 1
      rw [Valuation.map_mul]
      refine mul_le_one' ?_ (hc2 v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (coe_algebraMap_mem_adicCompletionIntegers v e)
    have := hd _ hint
    have e1 : pFin E ((Ideal.absNorm (Ideal.span {d}) : A E) * c) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2) := by
      have e2 : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : FiniteAdeleRing (𝓞 E) E) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) := by
        rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
      rw [map_mul, map_natCast, e2, mul_assoc, ← mul_assoc (algebraMap E _ _) (algebraMap E _ _), mul_comm (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e)), mul_assoc]
      rfl
    rw [e1]
    exact this
  obtain ⟨k, hk⟩ : ∃ k, k = GeneralLinearGroup.map (pFin E) κ := ⟨_, rfl⟩
  have hκk : κ = finGL E 2 k := by
    have h1 : GeneralLinearGroup.map (pInf E) κ = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      obtain ⟨⟨c, hc, hcx⟩, -⟩ := hκ i j
      have h0 : pInf E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) = 0 := by
        rw [hcx]
        exact pInf_zero _ (by
          change ((Ideal.absNorm (Ideal.span {d}) : A E)).1 * c.1 = 0
          rw [hc.1, mul_zero])
      rw [map_sub, sub_eq_zero] at h0
      change pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rw [h0]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := infGL_mul_finGL κ
    rw [h1, map_one, one_mul, ← hk] at this
    exact this.symm
  have hkV : l⁻¹ * k * l ∈ {k | GlobalTheory.CuspRep.finRep E 2 k f = f} := by
    refine hWk k (fun i j => ?_) (fun i j => ?_)
    · obtain ⟨⟨c, hc, hcx⟩, -⟩ := hκ i j
      have := hent _ c hc hcx
      have e : k.val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
        rw [map_sub, hk]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e]; exact this
    · obtain ⟨-, ⟨c, hc, hcx⟩⟩ := hκ i j
      have := hent _ c hc hcx
      have e : (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((κ⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
        rw [map_sub, hk, ← map_inv]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e]; exact this
  have hfix : f.1 (g * h * finGL E 2 (l⁻¹ * k * l)) = f.1 (g * h) := congrFun (congrArg Subtype.val hkV) (g * h)
  rw [← hfix, hκk, hh]
  congr 1
  simp only [map_mul, map_inv, mul_assoc]
  rw [← mul_assoc (finGL E 2 k), ← infGL_comm]
  simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsSmoothLieActionMemCuspidalTranslates
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem rt_infGL_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) =
      lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z))
    (Units.inv_mul_cancel_right (y.val * X) y).symm

private theorem lie_rt_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (X : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (A E)) :
    ∃ Y : Lie E a, lie E a (toL X) * rt E a h = rt E a h * lie E a Y := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) h with hy
  set κ := Matrix.GeneralLinearGroup.map (pFin E) h with hκ
  have hh : h = infGL E a y * finGL E a κ := (infGL_mul_finGL h).symm
  refine ⟨toL ((y⁻¹).val * X * y.val), ?_⟩
  have e : y.val * ((y⁻¹).val * X * y.val) * (y⁻¹).val = X := by
    simp [Matrix.mul_assoc]
  have key := rt_infGL_lie y ((y⁻¹).val * X * y.val)
  rw [e] at key
  conv_lhs => rw [hh, map_mul, ← mul_assoc, ← key, mul_assoc, lie_rt_fin, ← mul_assoc]
  rw [← map_mul, ← hh]

theorem UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (X : Lie E 2) (φ : GL (Fin 2) (A E) → ℂ), φ ∈ Tr P → ∃ f : Sm E 2, f.1 = φ ∧ (lie E 2 X f).1 ∈ Tr P := by
  intro E _ _ _ P X φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, hf, h, rfl⟩ := hφ
    obtain ⟨Y, hY⟩ := lie_rt_eq (a := 2) (E := E) X h
    refine ⟨rt E 2 h ⟨f.1, f.2⟩, rfl, ?_⟩
    have e : lie E 2 X (rt E 2 h f) = rt E 2 h (lie E 2 Y f) := LinearMap.congr_fun hY f
    have hm : lie E 2 Y f ∈ P.V := P.stable (.lie Y) f hf
    refine Submodule.subset_span ⟨_, hm, h, ?_⟩
    rw [show (⟨f.1, f.2⟩ : Sm E 2) = f from rfl, e]
    rfl
  | zero => exact ⟨0, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨fa, rfl, ha⟩ := ha
    obtain ⟨fb, rfl, hb⟩ := hb
    refine ⟨fa + fb, rfl, ?_⟩
    rw [map_add]
    exact (Tr P).add_mem ha hb
  | smul c a _ ha =>
    obtain ⟨fa, rfl, ha⟩ := ha
    refine ⟨c • fa, rfl, ?_⟩
    rw [map_smul]
    exact (Tr P).smul_mem c ha
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsUnipotentDiagRotationLevelDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem kgl_of {v : H.P ℚ} (y : GL (Fin 2) (H.Kv v)) (h1 : ∀ i j, y.val i j ∈ Formalism.UG.Ov ℚ v)
    (h2 : ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov ℚ v) : y ∈ GlobalTheory.LFun.KGL v 2 := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  let M : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map (Formalism.UG.Ov ℚ v).subtype = y.val := by ext i j; rfl
  have hN : N.map (Formalism.UG.Ov ℚ v).subtype = (y⁻¹).val := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) => A.map (Formalism.UG.Ov ℚ v).subtype) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
  · simp only
    rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · simp only
    rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · exact hM

private theorem cp_rot (v : H.P ℚ) (t : ℝ) : Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  have h : Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1 := TR.pFin_infGL _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := congrArg (fun x : GL (Fin 2) (Af ℚ) => pLoc ℚ v (x.val i j)) h
  change H.cp v ((rot t).val i j) = _ at h2
  change H.cp v ((rot t).val i j) = _
  rw [h2]
  fin_cases i <;> fin_cases j <;> simp

private theorem lev_of (N : ℕ) (t : ℝ) (k : G1 ℚ)
    (hr : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (rot t))
    (hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1)
    (hd : ∀ v i j, Dv N v (k i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)) : Lev N ((rot t)⁻¹ * gl k) := by
  have e : ∀ v, Matrix.GeneralLinearGroup.map (H.cp v) ((rot t)⁻¹ * gl k) = Matrix.GeneralLinearGroup.map (H.cp v) (gl k) := by
    intro v
    rw [map_mul, map_inv, cp_rot, inv_one, one_mul]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · have h : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) ((rot t)⁻¹ * gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) 1 := by
      rw [map_mul, map_inv, hr, inv_mul_cancel, map_one]
    exact (TR.infEq ℚ).symm.injective (congrArg (fun x : GL (Fin 2) (TR.Rinf ℚ) => x.val i j) h)
  · unfold H.KAt
    rw [e]
    refine kgl_of _ (fun i j => hi v i j) fun i j => ?_
    rw [← map_inv, ← map_inv]
    change Valued.v (H.cp v ((k⁻¹ : G1 ℚ) i j)) ≤ 1
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases i <;> fin_cases j <;> simp [hi]
  · have h := congrArg (fun x : GL (Fin 2) (H.Kv v) => x.val i j) (e v)
    change H.cp v (((rot t)⁻¹ * gl k).val i j) = H.cp v (k i j) at h
    have h2 := hd v i j
    unfold Dv at h2 ⊢
    rw [map_sub] at h2 ⊢
    rw [h]; exact h2

private theorem pinf_re (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext w
  rw [Subsingleton.elim w Rat.infinitePlace]; rfl

private theorem real_rot (k : G1 ℚ) (hk : InfOrth k) (t : ℝ) (hs : re (k 1 0) = Real.sin t) (hc : re (k 1 1) = Real.cos t) :
    re (k 0 0) = Real.cos t ∧ re (k 0 1) = -Real.sin t := by
  let φ : A ℚ →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp (TR.pInf ℚ)
  have hφ : ∀ x, re x = φ x := fun _ => rfl
  have h1 : φ ((k.1 * k.1ᵀ) 0 1) = φ ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) 0 1) :=
    congrArg (fun x => (TR.infEq ℚ).symm x Rat.infinitePlace) (hk 0 1)
  have h2 := congrArg φ k.det_coe
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul, map_sub, map_one,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), map_zero] at h1 h2
  simp only [hφ] at hs hc ⊢
  rw [hs, hc] at h1 h2
  have h3 := Real.sin_sq_add_cos_sq t
  constructor
  · linear_combination (Real.sin t) * h1 + (Real.cos t) * h2 - φ (k 0 0) * h3
  · linear_combination (Real.cos t) * h1 - (Real.sin t) * h2 - φ (k 0 1) * h3

private theorem rot_of (k : G1 ℚ) (t : ℝ) (h0 : re (k 0 0) = Real.cos t) (h1 : re (k 0 1) = -Real.sin t)
    (hs : re (k 1 0) = Real.sin t) (hc : re (k 1 1) = Real.cos t) :
    Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (rot t) := by
  rw [rot, TR.pInf_infGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change TR.pInf ℚ (k i j) = _
  rw [pinf_re]
  fin_cases i <;> fin_cases j
  · exact congrArg (fun x _ => x) h0
  · exact congrArg (fun x _ => x) h1
  · exact congrArg (fun x _ => x) hs
  · exact congrArg (fun x _ => x) hc

private theorem loc {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (a b c d n : K)
    (ha : w a ≤ 1) (hb : w b ≤ 1) (hc : w c ≤ w n) (hd : w d ≤ 1) (hn : w n ≤ 1) (h : a * d - b * c = 1) :
    ∃ z z' β : K, z * z' = 1 ∧ w z = 1 ∧ w z' = 1 ∧ w β ≤ 1 ∧ w (z' * (a - β * c) - 1) ≤ w n ∧
      w (z' * (b - β * d)) ≤ w n ∧ w (z * c) ≤ w n ∧ w (z * d - 1) ≤ w n := by
  rcases hn.lt_or_eq with hn' | hn'
  · have hbc : w (b * c) ≤ w n := by
      rw [map_mul]; exact (mul_le_of_le_one_left' hb).trans hc
    have had : w a * w d = 1 := by
      rw [← map_mul, show a * d = 1 + b * c by linear_combination h]
      exact w.map_one_add_of_lt (hbc.trans_lt hn')
    have ha1 : w a = 1 := le_antisymm ha (had ▸ mul_le_of_le_one_right' hd)
    have hd1 : w d = 1 := by rwa [ha1, one_mul] at had
    have a0 : a ≠ 0 := by rintro rfl; simp at ha1
    have d0 : d ≠ 0 := by rintro rfl; simp at hd1
    refine ⟨a, a⁻¹, b / d, mul_inv_cancel₀ a0, ha1, by simp [ha1], by simpa [hd1] using hb, ?_, ?_, ?_, ?_⟩
    · rw [show a⁻¹ * (a - b / d * c) - 1 = -(b * c) / (a * d) by field_simp; ring]
      simpa [ha1, hd1] using hbc
    · rw [div_mul_cancel₀ _ d0]; simp
    · simpa [ha1] using hc
    · rw [show a * d - 1 = b * c by linear_combination h]; exact hbc
  · rw [hn'] at hc ⊢
    refine ⟨1, 1, 0, one_mul _, map_one _, map_one _, by simp, ?_, by simpa using hb, by simpa using hc, ?_⟩
    · simpa using w.map_sub_le ha (map_one w).le
    · simpa using w.map_sub_le hd (map_one w).le

theorem UpperTheory.exists_unipotent_diag_rotation_level_decomposition :
    ∀ (N : ℕ), 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        ∃ (b : A ℚ) (ζ : (A ℚ)ˣ) (κ : GL (Fin 2) (A ℚ)), ζ ∈ UU ∧ Lev N κ ∧ gl k = gl (nU b) * gl (mD ζ) * rot t * κ := by
  intro N _ k hk hS t hs hc
  obtain ⟨h0, h1⟩ := real_rot k hk.1 t hs hc
  have hdet := k.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hint : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v => natCast_mem (v.adicCompletionIntegers ℚ) N
  choose z z' β hzz hz hz' hβ e00 e01 e10 e11 using fun v : H.P ℚ =>
    loc (Valued.v (R := H.Kv v)) (H.cp v (k 0 0)) (H.cp v (k 0 1)) (H.cp v (k 1 0)) (H.cp v (k 1 1)) (N : H.Kv v)
      (hint v 0 0) (hint v 0 1) (hS v) (hint v 1 1) (hN v)
      (by rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one])
  let Z : A ℚ := ((1, ⟨z, Eventually.of_forall fun v => (hz v).le⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  let Z' : A ℚ := ((1, ⟨z', Eventually.of_forall fun v => (hz' v).le⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  let B : A ℚ := ((0, ⟨β, Eventually.of_forall fun v => hβ v⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  have hZ : ∀ v, H.cp v Z = z v := fun _ => rfl
  have hZ' : ∀ v, H.cp v Z' = z' v := fun _ => rfl
  have hB : ∀ v, H.cp v B = β v := fun _ => rfl
  have hZZ : Z * Z' = 1 := Prod.ext (mul_one _) (FiniteAdeleRing.ext _ fun v => hzz v)
  have rZ : TR.pInf ℚ Z = 1 := map_one (TR.infEq ℚ).symm
  have rZ' : TR.pInf ℚ Z' = 1 := map_one (TR.infEq ℚ).symm
  have rB : TR.pInf ℚ B = 0 := map_zero (TR.infEq ℚ).symm
  let ζ : (A ℚ)ˣ := ⟨Z, Z', hZZ, (mul_comm _ _).trans hZZ⟩
  let k' : G1 ℚ := ⟨!![Z' * (k 0 0 - B * k 1 0), Z' * (k 0 1 - B * k 1 1); Z * k 1 0, Z * k 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (k 0 0 * k 1 1 - k 0 1 * k 1 0) * hZZ + hdet⟩
  have hd : ∀ v i j, Dv N v (k' i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    intro v i j
    unfold Dv
    fin_cases i <;> fin_cases j
    · simpa [k', hZ, hZ', hB] using e00 v
    · simpa [k', hZ, hZ', hB] using e01 v
    · simpa [k', hZ, hZ', hB] using e10 v
    · simpa [k', hZ, hZ', hB] using e11 v
  refine ⟨B, ζ, (rot t)⁻¹ * gl k', ⟨rfl, fun v => hz v⟩, lev_of N t k' (rot_of k' t ?_ ?_ ?_ ?_) (fun v i j => ?_) hd, ?_⟩
  · simpa [k', re, rZ, rZ', rB] using h0
  · simpa [k', re, rZ, rZ', rB] using h1
  · simpa [k', re, rZ, rZ', rB] using hs
  · simpa [k', re, rZ, rZ', rB] using hc
  · have h := (hd v i j).trans (hN v)
    rw [← sub_add_cancel (k' i j) ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j), map_add]
    refine Valuation.map_add_le _ h ?_
    fin_cases i <;> fin_cases j <;> simp
  · rw [mul_assoc, mul_inv_cancel_left, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    change _ = (!![1, B; 0, 1] * !![Z, 0; 0, Z'] *
      !![Z' * (k 0 0 - B * k 1 0), Z' * (k 0 1 - B * k 1 1); Z * k 1 0, Z * k 1 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-k 0 0) * hZZ
    · linear_combination (-k 0 1) * hZZ
    · linear_combination (-k 1 0) * hZZ
    · linear_combination (-k 1 1) * hZZ
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerCoeffNeZeroOfAdmissible
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

open GroundTheory.Automorphic.FourierWhittaker in

private noncomputable def latQ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    vecLattice ℚ (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap ℚ E (ξ 0) + algebraMap ℚ E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

open GroundTheory.Automorphic.FourierWhittaker in

private theorem int_zero {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (H : A E → ℂ)
    (hper : ∀ (k : E) x, H (rt k + x) = H x)
    (h0 : ∫ u in FS2 ℚ, H (D.mkE (u 0) (u 1)) ∂(adeleMeasurePi ℚ) = 0) :
    ∫ x in fundamentalSet E, H x ∂(adeleMeasure E) = 0 := by
  let β : (Fin 2 → A ℚ) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi ℚ (ι := Fin 2)).IsAddHaarMeasure :=
    inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure ℚ).IsAddHaarMeasure
  haveI : ((adeleMeasurePi ℚ (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi ℚ)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ)
      ((adeleMeasurePi ℚ (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := ℚ) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latQ D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hp : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E), H (g +ᵥ x) = H x := by
    rintro ⟨_, k, rfl⟩ x
    exact hper k x
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latQ D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := H) hp
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]
  have h3 : ∫ u in FS2 ℚ, H (m u) ∂(adeleMeasurePi ℚ) = 0 := h0
  rw [h3, smul_zero]

private theorem exists_mul {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    ∃ ξ : Eˣ, ∀ z : A E, ψ (rt (ξ : E) * z) = ψ (D.co z 1) := by
  let χ : AddChar (A E) Circle :=
    { toFun := fun z => adelicChar ℚ (D.co z 1)
      map_zero_eq_one' := by rw [D.co_zero]; simp
      map_add_eq_mul' := fun a b => by rw [D.co_add, Pi.add_apply, AddChar.map_add_eq_mul] }
  have h1 : Continuous fun z : A E => D.co z 1 := (continuous_apply 1).comp D.continuous_co
  have h2 : Continuous fun z : A E => adelicChar ℚ (D.co z 1) := (continuous_adelicChar (K := ℚ)).comp h1
  have hχ : Continuous χ := h2
  obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul (K := E) χ hχ fun k => by
    change adelicChar ℚ (D.co (rt k) 1) = 1
    rw [D.co_rt]
    exact adelicChar_algebraMap _
  have h0 : ξ ≠ 0 := by
    rintro rfl
    apply adelicChar_ne_one (K := ℚ)
    refine DFunLike.ext _ _ fun t => ?_
    have := hξ (D.mkE 0 t)
    change adelicChar ℚ (D.co (D.mkE 0 t) 1) = _ at this
    rw [D.co_mkE] at this
    simpa using this
  refine ⟨Units.mk0 ξ h0, fun z => ?_⟩
  have := hξ z
  change adelicChar ℚ (D.co z 1) = _ at this
  simp only [ψ, Units.val_mk0]
  rw [this]

theorem UpperTheory.exists_whittakerCoeff_ne_zero_of_admissible :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω : HChar ℚ), (∀ φ ∈ Tr P, admitted D ω φ) → ∃ f ∈ P.V, ∃ h, Wo D f.1 h ≠ 0 := by
  intro E _ _ _ D P ω hA
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  refine ⟨f, hf, ?_⟩
  by_contra hn
  push Not at hn
  have hT : f.1 ∈ Tr P := Submodule.subset_span ⟨f, hf, 1, by simp⟩
  have hL : Pp.Lf f.1 := ⟨(hA _ hT).cont, (hA _ hT).left⟩
  obtain ⟨ξ, hξ⟩ := exists_mul D
  have hW : ∀ g, Wf f.1 g = 0 := fun g => by
    have e := Pp.wfT E f.1 hL ξ ((aE (IdeleGroup.diagonal E ξ))⁻¹ * g)
    rw [mul_inv_cancel_left] at e
    rw [← e]
    refine int_zero D _ (fun k x => ?_) ?_
    · rw [hL.per, mul_add, ← map_mul, Pp.ψ_add, Pp.ψ_rt, one_mul]
    · rw [← hn ((aE (IdeleGroup.diagonal E ξ))⁻¹ * g)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      rw [hξ, D.co_mkE]
      rfl
  obtain ⟨φ, rfl⟩ := Cm.mem_range_ofCusp.2 (P.cusp f hf)
  exact h0 (Subtype.ext (Pp.eq_zero_of_Wf φ.2 hL hW))
end

