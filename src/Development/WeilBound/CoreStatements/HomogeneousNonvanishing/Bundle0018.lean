import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0016
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfB
import CompanionTheory.AutomorphicTheory.KrullDimension.TopologicalKrullDimModel

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MulEqOneOfComb
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.CompHt

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem mul_eq_one_of_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V] {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (c : Matrix (Fin n) (Fin N) K)
    (h : ∀ j, b j = ∑ k, c k j • ∑ i, g i k • b i) : g * c = 1 := by
  ext i j
  have e := congrArg (fun v => b.repr v i) (h j)
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [mul_comm (g i _), ← e, eq_comm]

theorem sum_eq {K : Type} [Field K] (σ : K →+* ℂ) {N n : ℕ} {g : Matrix (Fin N) (Fin n) K}
    {c : Matrix (Fin n) (Fin N) K} (h : g * c = 1) (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) (a : Fin N) :
    ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j = ∑ m, A m a * x m := by
  have e : ∀ j m, ∑ k, σ (g j k) * σ (c k m) = if j = m then 1 else 0 := fun j m => by
    have := congrArg σ (congrFun (congrFun h j) m)
    rw [Matrix.mul_apply, map_sum, Matrix.one_apply, apply_ite σ, map_one, map_zero] at this
    simpa only [map_mul] using this
  calc ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j
      = ∑ j, ∑ m, (∑ k, σ (g j k) * σ (c k m)) * (A m a * x j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by simp [e]

theorem isometric_fs {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (M : RatModel (𝓞 K) Ω) (L : HermLB M.s)
    (ev : V →ₗ[K] Ω) {W : Submodule (𝓞 K) V} (s : W → L.B.Sec) {e : L.B.ι → Ω}
    (hv : ∀ w : W, M.HasVal e (s w) (ev w)) (hW : Submodule.span K (W : Set V) = ⊤) {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (hgw : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hcb : ∀ j, b j = ∑ k, c k j • (gw k : V))
    (hφ : ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts M.s (σ.comp (algebraMap (𝓞 K) K))),
      (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2))
    (hs : ⨆ k, nonzeroLocus (s (gw k)) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hdet hcc)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    (t : ℝ) :
    ((HermLB.fs M.s L.isLB (fun k => s (gw k)) hs Mt hdet hcc).shift (fun _ => t) (fun _ => rfl)).Isometric
      (L.shift (fun _ => t) (fun _ => rfl)) := by
  have hgc := mul_eq_one_of_comb b g c fun j => by simpa only [hgw] using hcb j
  refine HermLB.isometric_of_eqOn fun σ' l y hl => ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' := ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
  replace hl : y ∈ ptsIn M.s _ (L.B.U l) := hl
  have hz := mem_ptsIn.1 hl
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hW fun v hvW => by
    rw [← hv ⟨v, hvW⟩ l ⟨_, hz⟩]
    exact valF_mem_O hz _
  have hr : Set.range y.1 ⊆ L.B.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
  have hsk : ∀ k, valR y.1 (L.B.U l) ((s (gw k)).f l) = ∑ j, σ (g j k) * x j := fun k => by
    refine ((val_eq hr (hv (gw k) l ⟨_, hz⟩)).symm.trans (hx _)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgw, b.repr_sum_self]
  refine congrArg (· + 2 * t) ((hφ σ l y).trans (Eq.trans ?_
    (Weight.fsBasis_φ L.isLB (fun k => s (gw k)) hs _ (hdet _) l y).symm))
  simp only [hsk, hMt, sum_eq σ hgc]
  rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)]

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFFromSpecStalk
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ZH

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem valF_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)) :
    valF (F := X.functionField) (X.fromSpecStalk (genericPoint X)) U f = fnOf U h f := by
  have hsp : ∀ w, (X.fromSpecStalk (genericPoint X)).base w ⤳ genericPoint X := by
    intro w
    have hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hw
    exact hw
  have hU : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U := by
    intro w _
    exact (hsp w).mem_open U.isOpen h
  have key : Scheme.Hom.appLE (X.fromSpecStalk (genericPoint X)) U ⊤ hU ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom = X.presheaf.germ U (genericPoint X) h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, homOfLE_comp, homOfLE_refl, op_id,
      Functor.map_id, Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
    simp
  unfold valF
  rw [dif_pos hU]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ f) key

private theorem top_le_map_fromSpecStalk_genericPoint (X : Scheme.{0}) [IsIntegral X] (U : X.Opens)
    (h : genericPoint X ∈ U) : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U := by
  intro w _
  have hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hw
  exact hw.mem_open U.isOpen h

private theorem valF_spMap_comp' {K L : Type} [Field K] [Field L] (σ : K →+* L) {Y : Scheme.{0}}
    (y : Sp K ⟶ Y) (U : Y.Opens) (hy : ⊤ ≤ (Opens.map y.base).obj U) (f : Γ(Y, U)) :
    valF (spMap σ ≫ y) U f = σ (valF y U f) := by
  have h2 : ⊤ ≤ (Opens.map (spMap σ ≫ y).base).obj U := fun w _ => hy (Opens.mem_top ((spMap σ).base w))
  have k2 : Scheme.Hom.appLE (spMap σ) ⊤ ⊤ (fun _ _ => trivial) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom σ := by
    have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
    convert hn using 2
    exact Scheme.Hom.appLE_eq_app (spMap σ) (U := ⊤)
  unfold valF
  rw [dif_pos h2, dif_pos hy, ← Scheme.Hom.appLE_comp_appLE (spMap σ) y U ⊤ ⊤ hy (fun _ _ => trivial)]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (CommRingCat.Hom.hom (Scheme.Hom.appLE y U ⊤ hy) f)) k2

theorem exists_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp o)
    (ψ : Ω →+* X.functionField) (hψ : Function.Bijective ψ)
    (hb : ∀ a : o, ψ (algebraMap o Ω a) = fnOf ⊤ (Opens.mem_top _) (algX p ⊤ a)) :
    ∃ pt : Sp Ω ⟶ X, pt ≫ p = spMap (algebraMap o Ω) ∧ Set.range pt = {genericPoint X} ∧
      (∀ x : Ω, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)), ψ (valF pt U f) = fnOf U h f := by
  let e : Ω ≃+* X.functionField := RingEquiv.ofBijective ψ hψ
  let σ : X.functionField →+* Ω := e.symm.toRingHom
  have H4 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)),
      ψ (valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) U f) = fnOf U h f := by
    intro U h f
    rw [valF_spMap_comp' σ _ U (top_le_map_fromSpecStalk_genericPoint X U h) f, valF_fromSpecStalk X U h f]
    exact e.apply_symm_apply _
  have hval : ∀ a : o, valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ (algX p ⊤ a) = algebraMap o Ω a := by
    intro a
    apply hψ.1
    rw [H4 ⊤ (Opens.mem_top _) (algX p ⊤ a), hb a]
  have hrange : ∀ w, (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base w = genericPoint X := by
    intro w
    have hw : (X.fromSpecStalk (genericPoint X)).base ((spMap σ).base w) ∈
        Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hw
    exact (Specializes.antisymm hw ((genericPoint_spec ↥X).specializes trivial)).eq
  refine ⟨(spMap σ ≫ X.fromSpecStalk (genericPoint X)), ?_, ?_, ?_, H4⟩
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of o)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom]
    have hR : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ (spMap (algebraMap o Ω)).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω) := by
      rw [spMap, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have hL : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ ((spMap σ ≫ X.fromSpecStalk (genericPoint X)) ≫ p).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω) := by
      ext a
      change _ = algebraMap o Ω a
      rw [← hval a]
      have q1 : Scheme.Hom.appLE p ⊤ ⊤ (fun _ _ => trivial) = p.appTop := Scheme.Hom.appLE_eq_app p (U := ⊤)
      have q2 : Scheme.Hom.appLE (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ ⊤ (fun _ _ => trivial) = (spMap σ ≫ X.fromSpecStalk (genericPoint X)).appTop :=
        Scheme.Hom.appLE_eq_app _ (U := ⊤)
      unfold valF algX
      rw [dif_pos (show ⊤ ≤ (Opens.map (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base).obj ⊤ from fun _ _ => trivial),
        q1, q2]
      rfl
    simp only [Category.assoc] at hL hR ⊢
    rw [hL, hR]
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨IsLocalRing.closedPoint Ω, hrange _⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hrange w
  · intro x
    obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (ψ x)
    refine ⟨V, s, ⟨_, hV⟩, hψ.1 ?_⟩
    rw [H4 V hV s]
    exact hs

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfOf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.FrameHeightScaling

theorem PositivityTheory.UnitarySelfGeneration.vuself_gen : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (t : ℝ), IsFrame Nm L b g A → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev d → ∀ (M : GlobalTheory.ZH.RatModel (𝓞 K) Ω), M.HasDiv (fun k => ev (∑ j, g j k • b j)) → GlobalTheory.IsArithVar M.s d → ∀ (H : ReciprocityTheory.ChartRestriction.G.Semi.LB M.Z) (hH : H.IsLB) (e : H.ι → Ω), M.GenTriv H e → ∀ (s : Fin m → H.Sec), (∀ k, M.HasVal e (s k) (ev (∑ j, g j k • b j))) → ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet : ∀ σ, (Mt σ).det ≠ 0) (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U), (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2) → ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => t) (fun _ => rfl)).IsSelfInter (((d : ℝ) + 1) * (Module.finrank ℚ K : ℝ) * (imageDeg ev d : ℝ) * (imageHeight Nm L ev d + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm L ev d N m b g A t hF hG hd M hNm hX H hH e he s hv hs Mt hdet hc hMt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hcomb := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.exists_comb ev b g hF.full
  obtain ⟨i, hi, -⟩ := hNm (genericPoint M.Z)
  have htop := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.closure_eq_top ev (fun k => ev (∑ j, g j k • b j))
    hcomb i hi hG.2
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  obtain ⟨Z, hZ, hZp⟩ := GlobalTheory.ZH.exists_isCl_isProjOver (𝓞 K) Ω n _ ⟨i, hi⟩ htop
  have hZX : GlobalTheory.IsArithVar Z.s d := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
    have h1 : Algebra.trdeg ℤ Ω = d :=
      (GlobalTheory.trdeg_eq_of_isAlgebraic_bot ℤ K Ω).trans (ModelDimension.ModelDim.trdeg_eq ev hG hd)
    refine ⟨inferInstance, inferInstance, inferInstance, hZp, (GlobalTheory.flat_int_iff_charZero _).2 ?_,
      ModelDimension.ModelDim.topologicalKrullDim_model inferInstance Z h1⟩
    exact (Z.res ⊤ ⟨genericPoint Z.Z, trivial⟩).charZero
  obtain ⟨π, hπ⟩ := hZ.exists_isHom (M' := M) (φ := AlgHom.id _ _) hNm
  obtain ⟨H', hH', e', s', he', hv', hs'⟩ := exists_bundle Z _ hZ.1
  obtain ⟨N', b', f', hf'⟩ := (imageDeg_pos_iff ev d).1 hd
  have hf := isChowFormInt_basis ev b' b hf'
  set f := GlobalTheory.ChowHt.linSubst (b'.toMatrix b) f'
  set δ := imageDeg ev d with hδ
  have hN : 0 < N := by
    obtain ⟨y, hy, -⟩ := hf.exists_point
    obtain ⟨j, -⟩ := Function.ne_iff.1 hy
    exact j.pos
  have hδ0 : ((d : ℝ) + 1) * δ ≠ 0 := mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hd.ne')
  have hh : imageHeight Nm L ev d = GlobalTheory.ChowHt.formHeight δ g A f / (((d : ℝ) + 1) * δ) :=
    GlobalTheory.ImageHeightUnique.imageHeight_eq K V Ω Nm L ev d _
      ⟨N, _, b, g, A, δ, f, hF, hf, mul_div_cancel₀ _ hδ0⟩
  have hc0 : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
  have ht : (fun k => ev (∑ j, g j k • b j)) = fun k => ∑ j, algebraMap K Ω (g j k) * ev (b j) := funext fun k => by
    simp only [map_sum, map_smul, Algebra.smul_def]
  have hdet' : ∀ σ, (((Real.exp t : ℝ) : ℂ) • Mt σ).det ≠ 0 := fun σ => by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hdet σ)
  have hc' : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ((Real.exp t : ℝ) : ℂ) • Mt ((starRingEnd ℂ).comp σ) =
      (((Real.exp t : ℝ) : ℂ) • Mt σ).map (starRingEnd ℂ) * U := fun σ => by
    obtain ⟨U, hU, h⟩ := hc σ
    refine ⟨U, hU, ?_⟩
    rw [h, ← smul_mul_assoc]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  have h1 := HP K Ω d N (n + 1) δ g (fun σ => ((Real.exp t : ℝ) : ℂ) • A σ) hF.full
    (fun σ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hF.herm σ))
    (conjCompat_smul hF.herm hF.conj hc0) (fun j => ev (b j)) Z (ht ▸ hZ) hZX f hf H' hH' e' he' s'
    (fun k => congrFun ht k ▸ hv' k) hs' (fun σ => ((Real.exp t : ℝ) : ℂ) • Mt σ) hdet' hc'
    (fun σ x => by rw [sum_smul, archSize_smul_sq, hMt])
  have h2 := (hP.p4.arProj _ _ _ Z.s M.s d hZX hX π hπ.inducedModelMorphism_comp_structureMap (map_generic hπ)
    (by rw [residueDegree_eq_one hπ]; exact one_ne_zero)).1 _ _ h1
  have h3 := (isometric_pull_fs hπ hH' he' hv' hs' hH he hv hs Mt _ hdet hc hdet' hc' t
    (fun _ => rfl)).isSelfInter hX h2
  convert h3 using 1
  rw [residueDegree_eq_one hπ, formHeight_smul hN g hF.herm hf.ne_zero hf.homog, hh]
  push_cast
  field_simp
end

