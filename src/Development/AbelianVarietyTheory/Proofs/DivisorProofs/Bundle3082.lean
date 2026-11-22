import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.MixNull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ChernNull

theorem chart_null_dom {k : Type} [CommRing k] [IsDomain k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (σ : k →+* ℂ) (hσ : Function.Injective σ) {D : ℕ} {Z : Set X} (hZ : IsClosed Z)
    (hgen : genericPoint X ∉ Z) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ hσ (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem part_compl_null : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ _ X _ p σ hσ _ D L ε U hU
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgen : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hU
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl
    fun c => by
      have e : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
        ext y
        simp [mem_ptsIn]
      rw [e]
      exact chart_null_dom σ hσ hZ hgen c

end GlobalTheory.MixNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open ReciprocityTheory.L2DbarEstimates (V cHess)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem MLine.Isom.hess_eq {L M : MLine p σ} (h : L.Isom M) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) {a : M.B.ι} {b : L.B.ι} (ha : y ∈ ptsIn p σ (M.B.U a)) (hb : y ∈ ptsIn p σ (L.B.U b)) :
    c.hess M.φ a y = c.hess L.φ b y := by
  obtain ⟨w, -, h⟩ := h
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (M.B.U a ⊓ L.B.U b),
      (ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 :=
    fun v hv => ev_ne_zero hv.2 (w.s _).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (L.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [h _ _ _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem dens_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) : dens L c y = dens M c y := by
  have e (i : Fin D) := (h i).hess_eq c hy (mem_pick (M i).φ.isLB y) (mem_pick (L i).φ.isLB y)
  simp only [dens, e]

theorem part_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (ε : ℤˣ) :
    part L ε = part M ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun ?_ ?_
  · exact measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) inter_subset_left
  · rintro _ ⟨y, hy, rfl⟩
    simp only [c.e.left_inv hy.1, dens_congr_isom h c hy.1]

theorem part_eq_of_isom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε :=
  fun _ _ _ _ _ _ _ _ _ h ε => part_congr_isom h ε

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosi
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

section
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder ComplexConjugate

theorem cHess_posSemidef_of_levi {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosSemidef := by
  classical
  set g : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g x) y) = leviV n g x (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

theorem re_sum_perm_det_nonneg {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    0 ≤ (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det).re := by
  have h := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hA).2
  have h0 : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have e : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det) =
      ((D.factorial : ℝ) : ℂ) * ReciprocityTheory.AnForm.mdisc A := by
    rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, Complex.ofReal_natCast, ← mul_assoc, mul_one_div_cancel h0, one_mul]
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

end

theorem dens_nonneg_of_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L : Fin D → MLine p σ} (h : ∀ i, (L i).φ.SemiPosReg D) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : 0 ≤ dens L c y :=
  mul_nonneg (by positivity) (re_sum_perm_det_nonneg (fun i => c.hess (L i).φ (pick (L i).φ.isLB y) y) fun i =>
    cHess_posSemidef_of_levi ((L i).cInf.contDiffAt c hy (mem_pick _ y)) (h i _ c y ⟨hy, mem_pick _ y⟩))

theorem part_neg_eq_zero_of_semiPosReg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  intro k _ X p σ _ D L h
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := dens_nonneg_of_semiPosReg h c (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaSpreadStableSummandLieDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem morita_spread_stable_summand_lie : ∀ {C : Type} [CommRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  (m : ℕ) [NeZero m] (E : Fin m → Fin m → Module.End C H),
  (∀ i j k l, E i j * E k l = if j = k then E i l else 0) → ∑ i, E i i = 1 →
  ∀ {A : Type} [CommRing A] (σ : A →+* Module.End C H), (∀ i j c, E i j * σ c = σ c * E i j) →
  ∀ {O : Type} [Ring O] (ρ : O →+* Module.End C H),
  (∀ (c : O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x → E 0 i (ρ c (E j 0 x)) ∈ N) →
  ∀ (e : Module.End C H), e * e = e → (∀ i j, E i j * e = e * E i j) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ i j, ∀ x ∈ F, E i j x ∈ F) → (∀ x ∈ F, e x ∈ F) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (G₀ M₀ : Submodule C H), G₀ ⊓ M₀ = ⊥ → G₀ ⊔ M₀ = LinearMap.range (E 0 0 * e) →
    (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) → G₀ ⊔ I • LinearMap.range (E 0 0 * e) = F ⊓ LinearMap.range (E 0 0 * e) →
    (∀ d ∈ LinearMap.range (E 0 0 * e), ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀) →
  ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : O), ∀ x ∈ G, ρ c x ∈ G) ∧
    G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧
    ∀ d ∈ LinearMap.range e, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  intro C _ I H _ _ m _ E hE hsum A _ σ hσ O _ ρ hρ e he heE F hIF hFE hFe a χ G₀ M₀ hGM hGM' hσG hGF hLie
  have mul_ap : ∀ (f g : Module.End C H) x, (f * g) x = f (g x) := fun _ _ _ => rfl
  have app : ∀ i j k l x, E i j (E k l x) = if j = k then E i l x else 0 := by
    intro i j k l x
    rw [← mul_ap, hE]; split_ifs <;> simp
  have eapp : ∀ i j x, E i j (e x) = e (E i j x) := by
    intro i j x; rw [← mul_ap, heE, mul_ap]
  have sigcomm : ∀ i j c x, σ c (E i j x) = E i j (σ c x) := by
    intro i j c x; rw [← mul_ap, ← hσ, mul_ap]
  have ee : ∀ x, e (e x) = e x := fun x => by rw [← mul_ap, he]
  have memRe : ∀ x, x ∈ LinearMap.range e ↔ e x = x := by
    intro x; constructor
    · rintro ⟨y, rfl⟩; exact ee y
    · intro h; exact ⟨x, h⟩
  have memR00 : ∀ x, x ∈ LinearMap.range (E 0 0 * e) ↔ E 0 0 x = x ∧ e x = x := by
    intro x; constructor
    · rintro ⟨y, rfl⟩
      simp only [mul_ap]
      refine ⟨?_, ?_⟩
      · rw [app]; simp
      · rw [← eapp, ee]
    · rintro ⟨h1, h2⟩; exact ⟨x, by rw [mul_ap, h2, h1]⟩
  have decomp : ∀ x, ∑ i, E i 0 (E 0 i x) = x := by
    intro x
    calc ∑ i, E i 0 (E 0 i x) = ∑ i, E i i x := by simp [app]
      _ = (∑ i, E i i) x := (LinearMap.sum_apply _ _ _).symm
      _ = x := by rw [hsum]; rfl
  have E0i_mem : ∀ i x, e x = x → E 0 i x ∈ LinearMap.range (E 0 0 * e) := by
    intro i x hx; rw [memR00]
    exact ⟨by rw [app]; simp, by rw [← eapp, hx]⟩
  have hG0R : ∀ x ∈ G₀, E 0 0 x = x ∧ e x = x := fun x hx =>
    (memR00 x).1 (by rw [← hGM']; exact Submodule.mem_sup_left hx)
  have hM0R : ∀ x ∈ M₀, E 0 0 x = x ∧ e x = x := fun x hx =>
    (memR00 x).1 (by rw [← hGM']; exact Submodule.mem_sup_right hx)
  have hG₀F : ∀ g ∈ G₀, g ∈ F := fun g hg => by
    have h : g ∈ G₀ ⊔ I • LinearMap.range (E 0 0 * e) := Submodule.mem_sup_left hg
    rw [hGF] at h; exact h.1
  have spread_in : ∀ (N : Submodule C H) k, ∀ g ∈ N, E k 0 g ∈ ⨆ i, N.map (E i 0) :=
    fun N k g hg => Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem hg)
  have spread_all : ∀ (N P : Submodule C H), (∀ k, ∀ g ∈ N, E k 0 g ∈ P) →
      (⨆ i, N.map (E i 0)) ≤ P :=
    fun N P h => iSup_le fun k => Submodule.map_le_iff_le_comap.2 fun g hg => h k g hg
  have spread_key : ∀ N : Submodule C H, (∀ x ∈ N, E 0 0 x = x) → ∀ j,
      ∀ x ∈ ⨆ i, N.map (E i 0), E 0 j x ∈ N := by
    intro N hN j x hx
    have : (⨆ i, N.map (E i 0)) ≤ N.comap (E 0 j) := by
      refine spread_all N _ fun k g hg => ?_
      simp only [Submodule.mem_comap]
      rw [app]
      split_ifs with h
      · subst h; rw [hN g hg]; exact hg
      · exact N.zero_mem
    exact this hx
  have spread_e : ∀ (N : Submodule C H), (∀ x ∈ N, e x = x) →
      (⨆ i, N.map (E i 0)) ≤ LinearMap.range e := fun N hN =>
    spread_all N _ fun k g hg => (memRe _).2 (by rw [← eapp, hN g hg])
  refine ⟨⨆ i, G₀.map (E i 0), ⨆ i, M₀.map (E i 0), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxG, hxM⟩
    have h0 : ∀ i, E 0 i x = 0 := fun i => by
      have : E 0 i x ∈ G₀ ⊓ M₀ :=
        ⟨spread_key G₀ (fun y hy => (hG0R y hy).1) i x hxG,
         spread_key M₀ (fun y hy => (hM0R y hy).1) i x hxM⟩
      rw [hGM] at this; exact (Submodule.mem_bot C).1 this
    rw [Submodule.mem_bot, ← decomp x]; simp [h0]
  · refine le_antisymm (sup_le (spread_e G₀ fun y hy => (hG0R y hy).2)
      (spread_e M₀ fun y hy => (hM0R y hy).2)) ?_
    intro x hx
    rw [memRe] at hx
    rw [← decomp x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : E 0 i x ∈ G₀ ⊔ M₀ := by rw [hGM']; exact E0i_mem i x hx
    obtain ⟨g, hg, n, hn, hgn⟩ := Submodule.mem_sup.1 h1
    rw [← hgn, map_add]
    exact Submodule.add_mem_sup (spread_in G₀ i g hg) (spread_in M₀ i n hn)
  · intro c x hx
    have key : ∀ j, E 0 j (ρ c x) ∈ G₀ := by
      intro j
      have : (⨆ i, G₀.map (E i 0)) ≤ G₀.comap (E 0 j * ρ c) :=
        spread_all G₀ _ fun k g hg => hρ c j k G₀ hσG g hg (hG0R g hg).1
      exact this hx
    rw [← decomp (ρ c x)]
    exact Submodule.sum_mem _ fun j _ => spread_in G₀ j _ (key j)
  · apply le_antisymm
    · refine sup_le ?_ (inf_le_inf_right _ hIF)
      refine spread_all G₀ _ fun k g hg => ⟨hFE k 0 g (hG₀F g hg), ?_⟩
      exact (memRe _).2 (by rw [← eapp, (hG0R g hg).2])
    · rintro x ⟨hxF, hxe⟩
      replace hxe := (memRe x).1 hxe
      rw [← decomp x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : E 0 i x ∈ F ⊓ LinearMap.range (E 0 0 * e) := ⟨hFE 0 i x hxF, E0i_mem i x hxe⟩
      rw [← hGF] at h1
      obtain ⟨g, hg, t, ht, hgt⟩ := Submodule.mem_sup.1 h1
      rw [← hgt, map_add]
      refine Submodule.add_mem_sup (spread_in G₀ i g hg) ?_
      have : I • LinearMap.range (E 0 0 * e) ≤ (I • ⊤ ⊓ LinearMap.range e).comap (E i 0) := by
        rw [Submodule.smul_le]
        intro r hr n hn
        rw [Submodule.mem_comap, map_smul]
        refine ⟨Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
        exact (memRe _).2 (by rw [map_smul, ← eapp, ((memR00 n).1 hn).2])
      exact this ht
  · intro d hd
    rw [memRe] at hd
    have hw : ∀ i, ∃ w : Fin a → H, (∀ j c, σ c (w j) - χ j c • w j ∈ G₀) ∧
        E 0 i d - ∑ j, w j ∈ G₀ := fun i => hLie _ (E0i_mem i d hd)
    choose w hw1 hw2 using hw
    refine ⟨fun j => ∑ i, E i 0 (w i j), ?_, ?_⟩
    · intro j c
      have : σ c (∑ i, E i 0 (w i j)) - χ j c • ∑ i, E i 0 (w i j) =
          ∑ i, E i 0 (σ c (w i j) - χ j c • w i j) := by
        simp only [map_sum, map_sub, map_smul, Finset.smul_sum, Finset.sum_sub_distrib, sigcomm]
      rw [this]; exact Submodule.sum_mem _ fun i _ => spread_in G₀ i _ (hw1 i j c)
    · have : d - ∑ j, ∑ i, E i 0 (w i j) = ∑ i, E i 0 (E 0 i d - ∑ j, w i j) := by
        conv_lhs => rw [← decomp d]
        rw [Finset.sum_comm]
        simp only [map_sub, map_sum, Finset.sum_sub_distrib]
      rw [this]; exact Submodule.sum_mem _ fun i _ => spread_in G₀ i _ (hw2 i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismLocalDescentsGlueUnion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem descend_glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  intro R _ _ _ _ S Y Z W π y p q hπp hπs hSi hy hpb O h I V hV h₀ hh
  have hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O := by
    rw [Scheme.Hom.preimage_iSup]; exact iSup_le hV
  haveI := hy
  have hflat : Flat ((⨆ i, V i).ι ≫ y) := inferInstance
  have hsq : IsPullback (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) ((⨆ i, V i).ι ≫ y) π :=
    (isPullback_morphismRestrict p (⨆ i, V i)).paste_vert hpb
  have loc : ∀ (i : I) (T : Scheme.{0}) (k : T ⟶ (p ⁻¹ᵁ (⨆ i, V i)).toScheme) (t : T ⟶ (V i).toScheme),
      k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι ≫ p = t ≫ (V i).ι → k ≫ Z.homOfLE hV' ≫ h = t ≫ h₀ i := by
    intro i T k t hkt
    have sq := isPullback_morphismRestrict p (V i)
    have w : t ≫ (V i).ι = (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) ≫ p := by rw [Category.assoc]; exact hkt.symm
    have h1 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ∣_ V i) = t := sq.lift_fst _ _ _
    have h2 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ⁻¹ᵁ V i).ι = k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι :=
      sq.lift_snd _ _ _
    have h3 : k ≫ Z.homOfLE hV' = sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ Z.homOfLE (hV i) := by
      rw [← cancel_mono O.ι]; simp [h2]
    rw [reassoc_of% h3, ← hh i, reassoc_of% h1]
  have heq : pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) =
      pullback.snd (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) := by
    let a : pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ⟶ Y :=
      pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι
    have hcov : TopologicalSpace.IsOpenCover (fun i => a ⁻¹ᵁ V i) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, eq_top_iff]
      intro x _
      have hx : a.base x ∈ Set.range (⨆ i, V i).ι.base := by
        have ha : a = (pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i))) ≫ (⨆ i, V i).ι :=
          (Category.assoc _ _ _).symm
        rw [ha]
        first
          | exact ⟨_, rfl⟩
          | (rw [Scheme.comp_base]; exact ⟨_, rfl⟩)
          | exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.Opens.range_ι] at hx
      exact hx
    refine Scheme.Cover.hom_ext ((pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i))).openCoverOfIsOpenCover _ hcov)
      _ _ fun i => ?_
    change (a ⁻¹ᵁ V i).ι ≫ _ = (a ⁻¹ᵁ V i).ι ≫ _
    rw [← Category.assoc, loc i _ _ (a ∣_ V i), ← Category.assoc, loc i _ _ (a ∣_ V i)]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι]
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq (Z.homOfLE hV' ≫ h) heq
  refine ⟨hV', m, hm, fun W' g g' hg => ?_⟩
  have key := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W' π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq ((p ∣_ (⨆ i, V i)) ≫ g)
    (by rw [pullback.condition_assoc])
  exact key.unique rfl hg.symm

end GlobalTheory.MorDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLiftStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i → ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  first | exact @GlobalTheory.Obs.mul_lifts | exact GlobalTheory.Obs.mul_lifts | (intros; apply GlobalTheory.Obs.mul_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  first | (exact @GlobalTheory.MulPolyNorm.eq_prod_aroots) | (exact GlobalTheory.MulPolyNorm.eq_prod_aroots) | (intros; apply GlobalTheory.MulPolyNorm.eq_prod_aroots  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  first | exact @GlobalTheory.PoincAdj.lbIso_adj_of_generic | exact GlobalTheory.PoincAdj.lbIso_adj_of_generic | (intros; apply GlobalTheory.PoincAdj.lbIso_adj_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem lamVal_axes_one : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF Z y z J J' hJ hJ'
  letI := D.P.isAb.comm
  have hpb := hF.1
  have hsq := hF.2.1
  have hw := hF.2.2.1
  have N := GlobalTheory.T.mumfordBundleIso_origin_one_of_generic_origin_domain T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB (spMap ω) β ββ w hpb hsq hw
    (GlobalTheory.T.mumfordBundleIso_generic_origin_one_tautologicalBase T ε n V D ω s e β ββ w hB hF)
  exact ⟨GlobalTheory.T.mumfordBundleIso_cartesianSquare_trivial_first_axis T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ',
    GlobalTheory.T.mumfordBundleIso_cartesianSquare_trivial_second_axis T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ'⟩

end GlobalTheory.TInj
end
end

