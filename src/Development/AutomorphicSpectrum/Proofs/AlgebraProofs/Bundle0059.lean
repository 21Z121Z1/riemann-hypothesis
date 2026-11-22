import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0048
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0057

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KahlerFormsOverSubalgebraClosureProperties
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem perDet_trace_mul_ext {E : Type} [Field E] [NumberField E] (u v : E)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) : u = v := by
  have hnd := traceForm_nondegenerate ℚ E
  apply ((Algebra.traceForm ℚ E).toDual hnd).injective
  apply (integralBasis E).ext
  intro i
  simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, integralBasis_apply] using
    h (RingOfIntegers.basis E i)

theorem perDet_exists_herm {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (x y : La) :
    ∃ u : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = ((EF (a • x) y : ℤ) : ℚ) := by
  have hnd := traceForm_nondegenerate ℚ E
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ
    (fun i => ((EF (RingOfIntegers.basis E i • x) y : ℤ) : ℚ))
  obtain ⟨u, hu⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective f
  refine ⟨u, fun a => ?_⟩
  have h1 : Algebra.trace ℚ E (u * a) = f a := by
    have := LinearMap.congr_fun hu (a : E)
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using this
  rw [h1]
  let L1 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom)
  let L2 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    { toFun := fun a => ((EF (a • x) y : ℤ) : ℚ)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }
  have hL : L1 = L2 := by
    apply (RingOfIntegers.basis E).ext
    intro i
    have hb : (algebraMap (𝓞 E) E) (RingOfIntegers.basis E i) = integralBasis E i :=
      (integralBasis_apply E i).symm
    change f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [hb]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun hL a

theorem perDet_exists_clear {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (v : E ⊗[𝓞 E] La) :
    ∃ (c : 𝓞 E) (x : La), c ≠ 0 ∧ ((c : E)) • v = (1 : E) ⊗ₜ[𝓞 E] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul e x =>
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    have hcE : (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc0
    refine ⟨c, b • x, hc0, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      smul_eq_mul, Algebra.smul_def (A := E) b (1 : E)]
    congr 1
    change algebraMap (𝓞 E) E c * _ = _
    field_simp
  | add v w hv hw =>
    obtain ⟨c, x, hc, hx⟩ := hv
    obtain ⟨d, y, hd, hy⟩ := hw
    refine ⟨c * d, d • x + c • y, mul_ne_zero hc hd, ?_⟩
    have hsm : ∀ (r : 𝓞 E) (t : La), (1 : E) ⊗ₜ[𝓞 E] (r • t) = ((r : E)) • ((1 : E) ⊗ₜ[𝓞 E] t) := by
      intro r t
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one, Algebra.smul_def, _root_.mul_one]
    rw [TensorProduct.tmul_add, hsm, hsm, ← hx, ← hy, smul_add, smul_smul, smul_smul]
    push_cast
    congr 2 <;> ring_nf

theorem perDet_det_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (EF : LinearMap.BilinForm ℤ La) (hinj : Function.Injective EF)
    (adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (bar a • y))
    (g : La →ₗ[𝓞 E] La) (hg : ∀ a b, EF (g a) (g b) = EF a b) :
    LinearMap.det (g.baseChange E) * IsCMField.complexConj E (LinearMap.det (g.baseChange E)) = 1 := by
  classical
  choose h hh using perDet_exists_herm (E := E) EF
  let σ : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hσ : ∀ c : 𝓞 E, σ (c : E) = ((bar c : 𝓞 E) : E) := fun c => (hbar c).symm
  have hbb : ∀ c : 𝓞 E, bar (bar c) = c := by
    intro c
    apply RingOfIntegers.ext
    rw [hbar, hbar]
    exact IsCMField.complexConj_apply_apply E _
  have h_add_l : ∀ x x' y, h (x + x') y = h x y + h x' y := fun x x' y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, smul_add, map_add, LinearMap.add_apply]
      push_cast
      rfl
  have h_add_r : ∀ x y y', h x (y + y') = h x y + h x y' := fun x y y' =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, map_add]
      push_cast
      rfl
  have h_smul_l : ∀ (c : 𝓞 E) x y, h (c • x) y = (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : (c : E) * h x y * (a : E) = h x y * ((a * c : 𝓞 E) : E) := by
        push_cast; ring
      rw [e1, hh, hh, smul_smul]
  have h_smul_r : ∀ (c : 𝓞 E) x y, h x (c • y) = σ (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : σ (c : E) * h x y * (a : E) = h x y * ((bar c * a : 𝓞 E) : E) := by
        rw [hσ]; push_cast; ring
      rw [e1, hh, hh, ← smul_smul, adj (bar c), hbb]
  have h_iso : ∀ x y, h (g x) (g y) = h x y := fun x y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [hh, hh, ← map_smul, hg]
  let f : La → (La →ₗ[𝓞 E] E) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => h_add_l x x' y
      map_smul' := fun c x => by
        rw [h_smul_l, RingHom.id_apply, Algebra.smul_def] }
  let F : La → ((E ⊗[𝓞 E] La) →ₗ[E] E) := fun y => LinearMap.liftBaseChange E (f y)
  have F_tmul : ∀ y (e : E) x, F y (e ⊗ₜ[𝓞 E] x) = e * h x y := by
    intro y e x
    simp only [F, LinearMap.liftBaseChange_tmul, smul_eq_mul]
    rfl
  have F_add : ∀ y y', F (y + y') = F y + F y' := by
    intro y y'
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x => rw [LinearMap.add_apply, F_tmul, F_tmul, F_tmul, h_add_r, mul_add]
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  have F_smul : ∀ (c : 𝓞 E) y, F (c • y) = σ (c : E) • F y := by
    intro c y
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x =>
      rw [LinearMap.smul_apply, F_tmul, F_tmul, h_smul_r, smul_eq_mul]
      ring
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  let f0 : E →+ La →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := AddMonoidHom.mk'
    (fun e => AddMonoidHom.mk' (fun y => σ e • F y) (fun y y' => by rw [F_add, smul_add]))
    (fun e e' => by
      ext y : 1
      simp [add_smul])
  let G : (E ⊗[𝓞 E] La) →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := TensorProduct.liftAddHom f0
    (fun r e y => by
      change σ (r • e) • F y = σ e • F (r • y)
      rw [F_smul, smul_smul, Algebra.smul_def, map_mul, _root_.mul_comm])
  have G_tmul : ∀ (e : E) y, G (e ⊗ₜ[𝓞 E] y) = σ e • F y := fun e y => rfl
  have G_smul : ∀ (c : E) w, G (c • w) = σ c • G w := by
    intro c w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul e y =>
      rw [TensorProduct.smul_tmul', G_tmul, G_tmul, smul_eq_mul, map_mul, smul_smul]
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
  let Hf : (E ⊗[𝓞 E] La) →ₗ[E] (E ⊗[𝓞 E] La) →ₛₗ[σ] E :=
    LinearMap.mk₂'ₛₗ (RingHom.id E) σ (fun v w => G w v)
      (fun v v' w => map_add _ _ _)
      (fun c v w => by rw [map_smul]; rfl)
      (fun v w w' => by rw [map_add, LinearMap.add_apply])
      (fun c v w => by rw [G_smul, LinearMap.smul_apply])
  have hHf : ∀ v w, Hf v w = G w v := fun _ _ => rfl
  have hnd : ∀ v, (∀ w, Hf v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, x, hc, hx⟩ := perDet_exists_clear v
    have hcE : (c : E) ≠ 0 := by simpa using hc
    have h0 : ∀ y, h x y = 0 := by
      intro y
      have h1 := hv ((1 : E) ⊗ₜ[𝓞 E] y)
      rw [hHf, G_tmul, map_one, one_smul] at h1
      have h2 : F y ((c : E) • v) = 0 := by rw [map_smul, h1, smul_zero]
      rw [hx, F_tmul, _root_.one_mul] at h2
      exact h2
    have hx0 : x = 0 := by
      apply hinj
      rw [map_zero]
      ext y
      have h3 := hh x y 1
      rw [h0 y] at h3
      simpa using h3.symm
    rw [hx0, TensorProduct.tmul_zero] at hx
    exact (smul_eq_zero.1 hx).resolve_left hcE
  have hiso : ∀ v w, Hf (g.baseChange E v) (g.baseChange E w) = Hf v w := by
    intro v w
    rw [hHf, hHf]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb]
    | tmul e y =>
      rw [LinearMap.baseChange_tmul, G_tmul, G_tmul, LinearMap.smul_apply, LinearMap.smul_apply]
      congr 1
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul e' x => rw [LinearMap.baseChange_tmul, F_tmul, F_tmul, h_iso]
  exact det_mul_map_det_eq_one_of_sesq σ Hf hnd (g.baseChange E) hiso

theorem per_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam a = a + l.M • e) → LinearMap.det ((gam : D.La →ₗ[𝓞 E] D.La).baseChange E) = 1 := by
  intro E _ _ _ H D l gam hiso hlev
  haveI := D.fin
  haveI := D.proj
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h1
    have h2 : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact h2 h1
  have h1mem : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨m', hm', m, hm, hmm⟩ := Submodule.mem_sup.1 h1mem
  have hcong : ∀ a, (gam : D.La →ₗ[𝓞 E] D.La) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    obtain ⟨e, he⟩ := hlev (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have h1 : m • gam a = m • a + ((l.M : ℕ) : 𝓞 E) • e := by
      rw [← map_smul, he, Nat.cast_smul_eq_nsmul]
    have h3 : gam a - a = m' • (gam a - a) + m • (gam a - a) := by
      rw [← add_smul, hmm, one_smul]
    have h4 : m • (gam a - a) = ((l.M : ℕ) : 𝓞 E) • e := by
      rw [smul_sub, h1, add_sub_cancel_left]
    rw [h4] at h3
    change gam a - a ∈ _
    rw [h3]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hm' Submodule.mem_top)
      (Submodule.smul_mem_smul hM Submodule.mem_top)
  obtain ⟨u, hu1, hu2⟩ := exists_det_congr_one E D.La l.Mb (gam : D.La →ₗ[𝓞 E] D.La) hcong
  have hdet := perDet_det_mul_conj H.bar H.bar_eq D.EF D.unimod.1 D.adj
    (gam : D.La →ₗ[𝓞 E] D.La) hiso
  rw [← hu2] at hdet ⊢
  obtain ⟨n, hn, hun⟩ := pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one E (u : E)
    (RingOfIntegers.isIntegral_coe u) hdet
  have hun' : u ^ n = 1 := RingOfIntegers.ext (by simpa using hun)
  have hu : u = 1 := root_eq_one_of_halfLevel E H.bar H.bar_eq l.Mb l.M l.three_le l.prod l.coprime
    u n hn hun' hu1
  rw [hu]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @PositivityTheory.HtPt.Siua.siu_kodaira | exact PositivityTheory.HtPt.Siua.siu_kodaira
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOrbitSelfStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_orbit_self' : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left), x ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | exact GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormNotMemPrimeIffStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_not_mem_prime_iff : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (e : B) (p : Ideal A), p.IsPrime → (Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q) := by
  first | exact @GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff | exact GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff | (intros; apply GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitTransStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_orbit_trans : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left), y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem isPullback_of_preimage_opensRange {X Y Y' : Scheme.{0}} (π : X ⟶ Y') (V : X.Opens)
    (q : V.toScheme ⟶ Y) (em : Y ⟶ Y') [IsOpenImmersion em] (hc : V.ι ≫ π = q ≫ em)
    (hpre : π ⁻¹ᵁ em.opensRange = V) : IsPullback q V.ι em π :=
  IsOpenImmersion.isPullback q V.ι em π hc (by rw [hpre, Scheme.Opens.opensRange_ι])

theorem IsChart.isIso_restrict_lift {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {π : X ⟶ Y'} {V : X.Opens}
    {q : V.toScheme ⟶ Y} {em : Y ⟶ Y'} [IsOpenImmersion em] (h : IsChart a b V q)
    (hc : V.ι ≫ π = q ≫ em) (hpre : π ⁻¹ᵁ em.opensRange = V) (w : a ≫ π = b ≫ π) :
    IsIso (pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V)) := by
  obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := h

  have h1 : IsPullback (b ∣_ V) (a' ≫ V.ι) (V.ι ≫ π) π := by
    have h0 := hsq.paste_horiz (isPullback_of_preimage_opensRange π V q em hc hpre).flip
    rw [← hc] at h0
    exact h0.flip

  have h2 : IsPullback (pullback.snd π π ∣_ V) ((pullback.snd π π ⁻¹ᵁ V).ι ≫ pullback.fst π π)
      (V.ι ≫ π) π :=
    (isPullback_morphismRestrict (pullback.snd π π) V).paste_vert (IsPullback.of_hasPullback π π).flip
  have hdom : pullback.lift a b w ⁻¹ᵁ (pullback.snd π π ⁻¹ᵁ V) = b ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_snd]

  have key : pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V) =
      (P.isoOfEq hdom).hom ≫ (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc]
      rw [IsPullback.isoIsPullback_hom_fst_assoc]
      simp only [morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.lift_snd,
        Scheme.isoOfEq_hom_ι_assoc]
    · rw [morphismRestrict_ι_assoc, pullback.lift_fst, Category.assoc,
        IsPullback.isoIsPullback_hom_snd, ha', Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance

theorem isPullback_of_isChart {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type}
    (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hch : ∀ j, IsChart a b (V j) (q j))
    (hc : ∀ j, (V j).ι ≫ π = q j ≫ em j) (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j)
    (hcov : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) : IsPullback a b π π := by

  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, z, hz⟩ := hcov (π x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨j, ?_⟩
    rw [← hpre j, Scheme.Hom.mem_preimage]
    exact ⟨z, hz⟩

  have hw : a ≫ π = b ≫ π := by
    refine Scheme.Cover.hom_ext
      (P.openCoverOfIsOpenCover (fun j => b ⁻¹ᵁ V j)
        (by unfold TopologicalSpace.IsOpenCover; exact b.iSup_preimage_eq_top hV)) _ _ fun j => ?_
    obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := hch j
    change (b ⁻¹ᵁ V j).ι ≫ a ≫ π = (b ⁻¹ᵁ V j).ι ≫ b ≫ π
    calc (b ⁻¹ᵁ V j).ι ≫ a ≫ π = a' ≫ (V j).ι ≫ π := by
          rw [← Category.assoc, ← ha', Category.assoc]
      _ = a' ≫ q j ≫ em j := by rw [hc j]
      _ = (b ∣_ V j) ≫ q j ≫ em j := by rw [← Category.assoc, hsq.w, Category.assoc]
      _ = (b ∣_ V j) ≫ (V j).ι ≫ π := by rw [hc j]
      _ = (b ⁻¹ᵁ V j).ι ≫ b ≫ π := by rw [morphismRestrict_ι_assoc]

  have hiso : IsIso (pullback.lift a b hw) := by
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun j => pullback.snd π π ⁻¹ᵁ V j) ((pullback.snd π π).iSup_preimage_eq_top hV)]
    intro j
    rw [MorphismProperty.isomorphisms.iff]
    exact IsChart.isIso_restrict_lift (hch j) (hc j) (hpre j) hw
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift a b hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackRestrictOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_restrict_open : ∀ {P Q Y S : Scheme.{0}} {c : P ⟶ Q} {v : P ⟶ Y} {g : Q ⟶ S} {p : Y ⟶ S}, IsPullback c v g p → ∀ (W : S.Opens) (D : Y.Opens), D ≤ p ⁻¹ᵁ W → ∃ (h : D.toScheme ⟶ W.toScheme) (u : (v ⁻¹ᵁ D).toScheme ⟶ (g ⁻¹ᵁ W).toScheme), IsPullback u (v ∣_ D) (g ∣_ W) h := by
  first | exact @GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens | exact GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens | (intros; apply GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShearIsoActionProjectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_iso_action_projection : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd | exact GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd <;> assumption)
end

