import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

theorem dense_of_span_real {g : ℕ} (S : Submodule ℚ (Fin g → ℂ))
    (hS : Submodule.span ℝ (S : Set (Fin g → ℂ)) = ⊤) : Dense (S : Set (Fin g → ℂ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : z ∈ Submodule.span ℝ (S : Set (Fin g → ℂ)) := hS ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem w hw => exact subset_closure hw
  | zero => exact subset_closure S.zero_mem
  | add a b _ _ ha hb => exact map_mem_closure₂ continuous_add ha hb fun c hc d hd => S.add_mem hc hd
  | smul t w _ hw =>

    have hq : ∀ q : ℚ, (q : ℝ) • w ∈ closure (S : Set (Fin g → ℂ)) := fun q =>
      map_mem_closure (continuous_const_smul (q : ℝ)) hw fun u hu => by
        rw [SetLike.mem_coe, Rat.cast_smul_eq_qsmul ℝ q u]
        exact S.smul_mem q hu
    have hcl : IsClosed {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    have hsub : closure (Set.range fun q : ℚ => (q : ℝ)) ⊆ {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      hcl.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact hq q)
    exact hsub ((Rat.denseRange_cast (𝕜 := ℝ)).closure_range ▸ Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

noncomputable def zRLin (x : Frame X.Ψ r) : WR X n →ₗ[ℝ] (Fin n → Fin g → ℂ) where
  toFun := zR X idx x
  map_add' u v := by
    funext k i
    simp only [zR, Pi.add_apply]
    split_ifs
    · simp [hermC, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' t v := by
    funext k i
    simp only [zR, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

theorem denseRange_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (pv X idx x) := by

  have hrange : ((LinearMap.range ((LinearMap.funLeft ℚ ℂ idx).comp (perLin X x)) :
      Submodule ℚ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range (pv X idx x) := by
    ext z
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    exact Iff.rfl
  unfold DenseRange
  rw [← hrange]
  apply dense_of_span_real
  rw [hrange]
  exact GlobalTheory.Dict.span_range_pv idx hs hx

theorem denseRange_zR_embR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (zR X idx x ∘ embR X (n := n)) := by
  have h : zR X idx x ∘ embR X (n := n) = fun y k => pv X idx x (y k) := by
    funext y k
    exact zR_embR X idx x y k
  rw [h]
  exact DenseRange.piMap fun _ => denseRange_pv X idx hs hx

theorem exists_equiv_zR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v := by

  have hsurj : Function.Surjective (zRLin X idx x (n := n)) := by
    have hcl : IsClosed (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    have hd : Dense (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      refine (denseRange_zR_embR X idx hs hx (n := n)).mono ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨embR X y, rfl⟩
    have huniv := hcl.closure_eq.symm.trans hd.closure_eq
    intro z
    have hz : z ∈ (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      rw [huniv]
      trivial
    exact LinearMap.mem_range.1 hz

  have hg : g = Fintype.card X.Ψ * r := by
    simpa [Fintype.card_prod] using Fintype.card_congr idx
  have hdim : Module.finrank ℝ (WR X n) = Module.finrank ℝ (Fin n → Fin g → ℂ) := by
    simp only [WR, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hg]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun v => rfl⟩

theorem EFR_embR (y y' : Matrix (Fin n) (Fin r) E) :
    EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ) := by
  have key : ∀ (τ : X.Ψ) (k : Fin n),
      hermC τ.1 X.Gm (embR X y τ k) (embR X y' τ k) = τ.1 (herm X.Gm (y k) (y' k)) :=
    fun τ k => ReciprocityTheory.ChartRestriction.G.FD.hermC_emb τ.1 X.Gm (y k) (y' k)
  rw [EFR, Rat.cast_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EF_def, GlobalTheory.UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [key, map_mul]

theorem zR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn x hxd
  obtain ⟨L, hL⟩ := exists_equiv_zR X idx (n := n) hs hxd
  have hlaws := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd

  have hD : DenseRange (embR X (n := n)) := by
    have h1 : embR X (n := n) = L.symm ∘ (zR X idx x ∘ embR X) := by
      funext y
      simp only [Function.comp_apply, ← hL, ContinuousLinearEquiv.symm_apply_apply]
    rw [h1]
    exact L.symm.surjective.denseRange.comp (denseRange_zR_embR X idx hs hxd) L.symm.continuous

  have hB : ∀ v v' : WR X n,
      (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v' := by
    have hc1 : Continuous fun p : WR X n × WR X n =>
        (∑ k, hx X bas idx x (zR X idx x p.1 k) (zR X idx x p.2 k)).im := by
      simp only [← hL, GlobalTheory.Dict.hx]
      fun_prop
    have hc2 : Continuous fun p : WR X n × WR X n => EFR X p.1 p.2 := by
      simp only [EFR, hermC]
      fun_prop
    have heq := (hD.prodMap hD).equalizer hc1 hc2 (by
      funext ⟨y, y'⟩
      simp only [Function.comp_apply, Prod.map_apply]
      rw [EFR_embR X y y', Complex.im_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zR_embR, zR_embR]
      exact hlaws.2.2.1 (y k) (y' k))
    exact fun v v' => congrFun heq (v, v')

  have hF : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n,
      zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) =
        zR X idx x v := by
    intro γ hγ
    have hA : Continuous fun v : WR X n =>
        (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k : WR X n) := by
      fun_prop
    have hc1 : Continuous fun v : WR X n =>
        zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) :=
      (LinearMap.continuous_of_finiteDimensional (zRLin X idx (lact γ x) (n := n))).comp hA
    have hc2 : Continuous fun v : WR X n => zR X idx x v := by
      simp only [← hL]
      exact L.continuous
    have heq := hD.equalizer hc1 hc2 (by
      funext y
      simp only [Function.comp_apply]
      have hemb : (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ embR X y τ k : WR X n) =
          embR X (Matrix.of fun k => (γ : Matrix (Fin r) (Fin r) E) *ᵥ y k) := by
        funext τ k
        exact (GlobalTheory.PerMove.emb_mulVec τ.1 _ (y k)).symm
      rw [hemb]
      funext k
      rw [zR_embR, zR_embR]
      exact (hlaws.2.2.2.2.2.2.2 γ hγ).2.1 (y k))
    exact fun v => congrFun heq v
  exact ⟨⟨L, hL⟩, hB, fun y y' => EFR_embR X y y', hD, hF⟩

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierUnitaryCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

private lemma mapL_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  simp

private lemma mapL_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (a b : GL (Fin r) E) (L : Lt E r) :
    mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [Matrix.mulVec_mulVec]

private lemma smul_left_cancel_of_ip_self_eq_one {n g : ℕ} {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) {a b : ℂ}
    (h : a • v = b • v) : a = b := by
  have ha := TensVac.ip_smul_left a hv hv
  have hb := TensVac.ip_smul_left b hv hv
  rw [h1, _root_.mul_one] at ha hb
  rw [← ha, ← hb, h]

theorem vac_multiplier_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  intro E _ _ _ r X g bas idx n hs hn D v₀ hvac mu hmu
  have hsd : SelfD X X.Λ := Lev.selfD_of_sympl hs
  have hlat : ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L ∈ D.lats := fun L hL ga hga =>
    Lev.mapL_mem_lats hsd hga hL
  have hred : ∀ ga ∈ D.grp, ∃ k : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k := by
    intro ga hga
    obtain ⟨-, k, hk, h⟩ := (Lev.mem_grp ga).mp hga
    exact ⟨⟨k, hk⟩, h⟩
  have hun : ∀ ga ∈ D.grp, IsUn X ga := fun ga hga => ((Lev.mem_grp ga).mp hga).1
  have hvsb : ∀ L ∈ D.lats, IsSB (v₀ L) := by
    intro L hL
    obtain ⟨h, -, -⟩ := hvac L hL
    exact h
  have hvone : ∀ L ∈ D.lats, ip (v₀ L) (v₀ L) = 1 := by
    intro L hL
    obtain ⟨-, h, -⟩ := hvac L hL
    exact h

  have hnorm : ∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1 := by
    intro ga hga L hL
    obtain ⟨k, hk⟩ := hred ga hga
    have hL' := hlat L hL ga hga
    have hip := ((wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ L) (hvsb L hL)).2.2.1
      (v₀ L) (hvsb L hL)).1
    rw [hmu ga hga L hL k hk, hvone L hL,
      TensVac.ip_smul_left _ (hvsb _ hL') (TensVac.sb_smul _ (hvsb _ hL')),
      TensVac.ip_smul_right _ (hvsb _ hL') (hvsb _ hL'), hvone _ hL', _root_.mul_one,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at hip
    have h2 : ‖mu ga L * ((D.lam k : ℂˣ) : ℂ)‖ ^ 2 = 1 := by exact_mod_cast hip
    rw [norm_mul, Lev.norm_lam k, _root_.mul_one] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

  have hlam : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ k k' k'' : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k →
      D.Red (fun i => (ga' : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k' →
      D.Red (fun i => ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k'' →
      ((D.lam k'' : ℂˣ) : ℂ) = (D.lam k : ℂˣ) * (D.lam k' : ℂˣ) := by
    intro ga _ ga' _ k k' k'' hk hk' hk''
    let y0 : Matrix (Fin r) (Fin r) E := Matrix.of fun i => D.β i
    have hy : ∀ M : Matrix (Fin r) (Fin r) E, y0 * Mᵀ = Matrix.of fun i => M *ᵥ D.β i := by
      intro M
      ext i j
      simp [y0, Matrix.mul_apply, Matrix.mulVec, dotProduct, _root_.mul_comm]
    have e1 := Lev.dat_lin (le_refl r) hk'' y0
    have e2 := Lev.dat_lin (le_refl r) hk (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ)
    have e3 := Lev.dat_lin (le_refl r) hk' y0
    have hne : D.dat (le_refl r) (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ) ≠ 0 := by
      rw [hy]
      unfold SW.Level.dat
      split_ifs with hc
      · exact Units.ne_zero _
      · exact absurd ⟨⟨k', hk'⟩, fun j hj => absurd j.isLt (not_lt.mpr hj)⟩ hc
    have hd0 : D.dat (le_refl r) y0 ≠ 0 := by
      intro h0
      apply hne
      rw [e3, h0]
      simp
    have hm : y0 * ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ =
        y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ * (ga : Matrix (Fin r) (Fin r) E)ᵀ := by
      rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm, e2, e3] at e1
    apply mul_right_cancel₀ hd0
    rw [← e1]
    ring

  have hcoc : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats,
      mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
    intro ga hga ga' hga' L hL
    obtain ⟨k, hk⟩ := hred ga hga
    obtain ⟨k', hk'⟩ := hred ga' hga'
    have hgg : ga * ga' ∈ D.grp := Subgroup.mul_mem _ hga hga'
    obtain ⟨k'', hk''⟩ := hred _ hgg
    have hL' := hlat L hL ga' hga'
    have hL'' := hlat _ hL' ga hga
    have hcomp := (wG_laws E r X g bas idx n hs hn ga' (hun ga' hga') (v₀ L)
      (hvsb L hL)).2.2.2.2.2.1 ga (hun ga hga)
    have hsm := (wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ (mapL ga' L))
      (hvsb _ hL')).2.2.2.1 (mu ga' L * ((D.lam k' : ℂˣ) : ℂ))
    rw [hmu _ hgg L hL k'' hk'', hmu ga' hga' L hL k' hk', hsm, hmu ga hga _ hL' k hk, smul_smul,
      mapL_mul'] at hcomp
    have hc := smul_left_cancel_of_ip_self_eq_one (hvsb _ hL'') (hvone _ hL'') hcomp
    rw [hlam ga hga ga' hga' k k' k'' hk hk' hk''] at hc
    have hk0 : ((D.lam k : ℂˣ) : ℂ) * (D.lam k' : ℂˣ) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    apply mul_right_cancel₀ hk0
    linear_combination hc
  refine ⟨hnorm, ?_, hcoc⟩

  intro L hL
  have h1 := hcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) L hL
  rw [_root_.mul_one, mapL_one'] at h1
  have hn1 := hnorm 1 (Subgroup.one_mem _) L hL
  have hne : mu 1 L ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  exact mul_left_cancel₀ hne (h1.symm.trans (_root_.mul_one _).symm)

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProductStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_preserves_theta_and_inner_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧ (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧ (∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ ∧ wG X bas idx γ (φ + ψ) = wG X bas idx γ φ + wG X bas idx γ ψ ∧ ∀ x ∈ X.dom, thA X bas idx φ x = thA X bas idx ψ x → φ = ψ) ∧ (∀ a : ℂ, wG X bas idx γ (a • φ) = a • wG X bas idx γ φ) ∧ wG X bas idx 1 φ = φ ∧ (∀ γ', IsUn X γ' → wG X bas idx (γ' * γ) φ = wG X bas idx γ' (wG X bas idx γ φ)) ∧ ∀ y : Matrix (Fin n) (Fin r) E, wG X bas idx γ (heisG X bas y φ) = heisG X bas (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ φ) := by
  first | exact @GlobalTheory.SW.wG_laws | exact GlobalTheory.SW.wG_laws | (intros; apply GlobalTheory.SW.wG_laws <;> assumption)
end

