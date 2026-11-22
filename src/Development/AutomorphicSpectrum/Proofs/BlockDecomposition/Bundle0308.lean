import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowMod
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem absNorm_span_modEq_one {F : Type} [Field F] [NumberField F] (l m : ℕ) {a : 𝓞 F} (ha : a ≠ 0)
    (ha1 : a - 1 ∈ powMod F l m) (hpos : ∀ σ : F →+* ℝ, 0 < σ (a : F)) :
    Ideal.absNorm (Ideal.span {a}) ≡ 1 [MOD l ^ m] := by
  have hn : 0 < Algebra.norm ℤ a := by
    have h := GlobalTheory.RayRootOfUnity.norm_pos_of_pos_real (x := (a : F)) (by simpa using ha) hpos
    rw [← Algebra.coe_norm_int] at h
    exact_mod_cast h
  have hc := GlobalTheory.Mem.RayNorm.norm_cast_eq F (l ^ m) (x := a) (y := 1) (by
    have e : ((l ^ m : ℕ) : 𝓞 F) = (l : 𝓞 F) ^ m := by push_cast; rfl
    rw [e]
    exact ha1)
  rw [map_one, Int.cast_one] at hc
  have h2 := congrArg (Int.cast : ℤ → ZMod (l ^ m)) (Int.natAbs_of_nonneg hn.le)
  rw [Int.cast_natCast] at h2
  rw [← ZMod.natCast_eq_natCast_iff, Ideal.absNorm_span_singleton, h2, hc, Nat.cast_one]

theorem absNorm_modEq_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)),
    RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  intro F _ _ l m I J h
  obtain ⟨a, b, ha, hb, ha1, hb1, hσ, he⟩ := h
  have h1 := absNorm_span_modEq_one l m ha ha1 fun σ => (hσ σ).1
  have h2 := absNorm_span_modEq_one l m hb hb1 fun σ => (hσ σ).2
  have h3 := congrArg Ideal.absNorm he
  rw [map_mul, map_mul] at h3
  calc Ideal.absNorm I = 1 * Ideal.absNorm I := (one_mul _).symm
    _ ≡ Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm I [MOD l ^ m] := h1.symm.mul_right _
    _ = Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm J := h3
    _ ≡ 1 * Ideal.absNorm J [MOD l ^ m] := h2.mul_right _
    _ = Ideal.absNorm J := one_mul _

end GlobalTheory.CompanionTheory.RayFacts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_equivariance_statement : PositivityTheory.RgDs.K.ActEquiv := by
  first | exact @GlobalTheory.CompanionTheory.ActEquivK.actEquiv | exact GlobalTheory.CompanionTheory.ActEquivK.actEquiv | (intros; apply GlobalTheory.CompanionTheory.ActEquivK.actEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgIntervalIntegralSwap
section
open GlobalTheory.CuspGeneric MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgSwap

private theorem integral_intervalIntegral_comm_of_continuous_norm_le {G : Type} [TopologicalSpace G]
    {mG : MeasurableSpace G} [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    (F : G × ℝ → ℂ) (hF : Continuous F) (t C : ℝ)
    (hC : ∀ x, ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖F (x, s)‖ ≤ C) :
    ∫ x, (∫ s in (0 : ℝ)..t, F (x, s)) ∂μ = ∫ s in (0 : ℝ)..t, ∫ x, F (x, s) ∂μ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hint : Integrable (Function.uncurry fun x s => F (x, s))
      (μ.prod (volume.restrict (Set.uIoc (0 : ℝ) t))) := by
    refine Integrable.mono' (integrable_const C) hF.aestronglyMeasurable ?_
    have hs : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.uIoc (0 : ℝ) t))), p.2 ∈ Set.uIoc (0 : ℝ) t :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hs] with p hp
    exact hC p.1 p.2 (Set.uIoc_subset_uIcc hp)
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [integral_smul]
  congr 1
  exact integral_integral_swap hint

theorem avg_intervalIntegral_swap {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ)
    (F : G × ℝ → ℂ) (hF : Continuous F) (hper : ∀ γ ∈ Γ, ∀ x s, F (γ + x, s) = F (x, s)) (t : ℝ) :
    avg Γ (fun x => ∫ s in (0 : ℝ)..t, F (x, s)) = ∫ s in (0 : ℝ)..t, avg Γ (fun x => F (x, s)) := by
  unfold GlobalTheory.CuspGeneric.IsCoLat at hΓ
  obtain ⟨-, K, hK, hKcov⟩ := hΓ
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_uIcc (a := (0 : ℝ)) (b := t))).exists_bound_of_continuousOn
    hF.continuousOn
  have hbound : ∀ x, ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖F (x, s)‖ ≤ C := by
    intro x s hs
    obtain ⟨γ, hγ, hγK⟩ := hKcov x
    rw [← hper γ hγ x s]
    exact hC (γ + x, s) ⟨hγK, hs⟩
  borelize G
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with h
  · try simp only [dif_pos h]
    haveI : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      ⟨by rw [Measure.restrict_apply_univ, h.choose_spec.2.2]; exact ENNReal.one_lt_top⟩
    exact integral_intervalIntegral_comm_of_continuous_norm_le _ F hF t C hbound
  · simp only [dif_neg h, intervalIntegral.integral_zero]

end GlobalTheory.CompanionTheory.AvgSwap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFactsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_weight_of_torus_facts : PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.BetaWeight := by
  first | exact @GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | exact GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | (intros; apply GlobalTheory.CompanionTheory.TorusSymbol.betaWeight <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLiftTensorCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section
namespace GlobalTheory.CompanionTheory.DisoHm
section Cmp
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_base {W : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU W T) (a : O) (r : R)
    (hr : κ a = Ideal.Quotient.mk I r) : ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i r) := by
  have e := evalAt_base q κ (show PtOver X q κ (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q κ (T.B ⧸ T.J) from T.y).2 h a
  refine e.trans ?_
  rw [hr]
  exact T.w r

theorem quot_eq_id {W : X.Opens} {d : ℕ} (c : Chart γ p q κ W d) (hW : IsAffineOpen W)
    (θ : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J)
    (h1 : ∀ r, θ (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r))
    (h2 : ∀ f, θ (ev c.D c.inV f) = ev c.D c.inV f) : θ = RingHom.id _ := by
  have key : ∀ θ' : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J,
      (∀ r, θ' (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r)) →
      (∀ f, θ' (ev c.D c.inV f) = ev c.D c.inV f) →
      (ptFun X q κ).map (CommRingCat.ofHom θ') c.D.y = c.D.y := by
    intro θ' a b
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have w := c.D.w r
      change θ' ((show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)) =
        (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)
      have w' : (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (c.D.i r) := w
      rw [w']
      exact a r
    · change Spec.map (CommRingCat.ofHom θ') ≫ pt c.D = pt c.D
      have e : Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec = pt c.D :=
        GlobalTheory.CompanionTheory.ChartAlg.eq_specMap hW (pt c.D) c.inV
      have e2 : θ'.comp (ev c.D c.inV) = ev c.D c.inV := RingHom.ext b
      calc Spec.map (CommRingCat.ofHom θ') ≫ pt c.D
          = Spec.map (CommRingCat.ofHom θ') ≫ Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec := by rw [e]
        _ = Spec.map (CommRingCat.ofHom (θ'.comp (ev c.D c.inV))) ≫ hW.fromSpec := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = pt c.D := by rw [e2, e]
  obtain ⟨g₀, -, hu⟩ := c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV
  exact (hu _ (key θ h1 h2)).trans (hu _ (key _ (fun _ => rfl) (fun _ => rfl))).symm

end Cmp

theorem cmp_bij : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  intro l _ O _ X q h W d c m cL hcL cO
  letI := (strV q W).toAlgebra
  intro e he het hev hT σ hσ
  let E : Γ(X, W) ≃+* cO.D.B := (Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv.trans e
  have hE : ∀ f, E f = e (1 ⊗ₜ f) := fun f => rfl
  have hEs : ∀ a, E (strV q W a) = cO.D.i a := fun a => by
    rw [hE, ← he]
    congr 1
    change (1 : O) ⊗ₜ[O] (algebraMap O Γ(X, W) a) = a ⊗ₜ 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hEt : ∀ i, E (c.t i) = cO.t i := het
  have hevE : ∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (E f) := hev
  let ψ : MvPolynomial (Fin d) O →+* cO.D.B := MvPolynomial.eval₂Hom cO.D.i cO.t
  have hψ : ψ.Etale := cO.etale
  let g : cO.D.B →+* cL.D.B ⧸ cL.D.J := (ev cL.D cL.inV).comp (E.symm : cO.D.B →+* Γ(X, W))
  let f₁ : MvPolynomial (Fin d) O →+* cL.D.B :=
    MvPolynomial.eval₂Hom (cL.D.i.comp (Ideal.Quotient.mk _)) cL.t
  have hg1 : ∀ f, g (E f) = ev cL.D cL.inV f := fun f => by
    change ev cL.D cL.inV (E.symm (E f)) = _
    rw [RingEquiv.symm_apply_apply]
  have hc : g.comp ψ = (Ideal.Quotient.mk cL.D.J).comp f₁ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have e1 : ψ (MvPolynomial.C a) = E (strV q W a) := by
        rw [hEs]; simp [ψ]
      have e2 : f₁ (MvPolynomial.C a) = cL.D.i (Ideal.Quotient.mk _ a) := by simp [f₁]
      change g (ψ (MvPolynomial.C a)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.C a))
      rw [e1, e2, hg1]
      exact ev_base cL.D cL.inV a _ rfl
    · have e1 : ψ (MvPolynomial.X i) = E (c.t i) := by
        rw [hEt]; simp [ψ]
      have e2 : f₁ (MvPolynomial.X i) = cL.t i := by simp [f₁]
      change g (ψ (MvPolynomial.X i)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.X i))
      rw [e1, e2, hg1]
      exact hcL i
  obtain ⟨H, ⟨hH1, hH2⟩, -⟩ := GlobalTheory.T.etale_lifting_of_nil_ideal cL.D.J (GlobalTheory.CompanionTheory.ChartMaps.nil_J cL.D) _ _ ψ hψ f₁ g hc
  have hHi : ∀ a, H (cO.D.i a) = cL.D.i (Ideal.Quotient.mk _ a) := fun a => by
    have := RingHom.congr_fun hH1 (MvPolynomial.C a)
    simpa [ψ, f₁] using this
  have hHt : ∀ i, H (cO.t i) = cL.t i := fun i => by
    have := RingHom.congr_fun hH1 (MvPolynomial.X i)
    simpa [ψ, f₁] using this
  have hHe : ∀ f, Ideal.Quotient.mk cL.D.J (H (E f)) = ev cL.D cL.inV f := fun f => by
    rw [← hg1, ← hH2]
    rfl
  have hk : ∀ a ∈ lm (l := l) cO.D m, H a = 0 := by
    have hle : lm (l := l) cO.D m ≤ RingHom.ker H := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change H ((l : cO.D.B) ^ m) = 0
      have e1 : (l : cO.D.B) ^ m = cO.D.i ((l : O) ^ m) := by
        rw [map_pow, map_natCast]
      rw [e1, hHi, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    exact fun a ha => hle ha
  let Hb : GB (l := l) cO.D m →+* cL.D.B := Ideal.Quotient.lift _ H hk
  have hHb : ∀ x, Hb (Ideal.Quotient.mk _ x) = H x := fun x => Ideal.Quotient.lift_mk _ H hk
  let mkG : cO.D.B →+* (GObj h cO.D m hT).B := Ideal.Quotient.mk (lm (l := l) cO.D m)
  have hV := inU_G h cO.D m hT cO.inV
  have hs : σ.φ.comp H = mkG := by
    have uniq := GlobalTheory.T.etale_lifting_of_nil_ideal (GObj h cO.D m hT).J (GlobalTheory.CompanionTheory.ChartMaps.nil_J (GObj h cO.D m hT)) _ _ ψ hψ
      (mkG.comp ψ) ((Ideal.Quotient.mk (GObj h cO.D m hT).J).comp mkG) rfl
    refine uniq.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · have e1 : ψ (MvPolynomial.C a) = cO.D.i a := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.C a))) = mkG (ψ (MvPolynomial.C a))
        rw [e1, hHi, σ.comm]
        rfl
      · have e1 : ψ (MvPolynomial.X i) = cO.t i := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.X i))) = mkG (ψ (MvPolynomial.X i))
        rw [e1, hHt, hσ]
        rfl
    · refine RingHom.ext fun x => ?_
      obtain ⟨f, rfl⟩ := E.surjective x
      have a1 := ev_G h cO.D m hT cO.inV hV f
      have a2 := ev_hom σ cL.inV hV f
      rw [hevE] at a1
      rw [← hHe] at a2
      exact a2.symm.trans a1
  have hs' : ∀ x, σ.φ (H x) = mkG x := fun x => RingHom.congr_fun hs x
  let ρ : cL.D.B →+* cL.D.B := Hb.comp σ.φ
  have hρH : ∀ x, ρ (H x) = H x := fun x => by
    change Hb (σ.φ (H x)) = H x
    rw [hs']
    exact hHb x
  have hρi : ∀ r, ρ (cL.D.i r) = cL.D.i r := fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← hHi, hρH]
  have hρt : ∀ i, ρ (cL.t i) = cL.t i := fun i => by
    rw [← hHt, hρH]
  have hle : cL.D.J ≤ cL.D.J.comap ρ := by
    intro x hx
    have : cL.D.J ≤ cL.D.J.comap ρ := by
      conv_lhs => rw [cL.J_eq]
      refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap, hρi, cL.J_eq]
      exact Ideal.mem_map_of_mem _ hr
    exact this hx
  have hθ : Ideal.quotientMap cL.D.J ρ hle = RingHom.id _ := by
    refine quot_eq_id cL c.affine _ (fun r => ?_) (fun f => ?_)
    · rw [Ideal.quotientMap_mk, hρi]
    · rw [← hHe, Ideal.quotientMap_mk, hρH]
  have hid : ρ = RingHom.id _ := by
    refine (GlobalTheory.CompanionTheory.ChartMaps.exists_unique_lift cL cL.D (RingHom.id _) (fun _ => rfl) cL.t (fun _ => rfl)).unique
      ⟨hρi, hρt, RingHom.ext fun x => ?_⟩ ⟨fun _ => rfl, fun _ => rfl, rfl⟩
    have := RingHom.congr_fun hθ (Ideal.Quotient.mk _ x)
    rw [Ideal.quotientMap_mk] at this
    exact this
  refine Function.bijective_iff_has_inverse.2 ⟨Hb, fun x => RingHom.congr_fun hid x, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) cO.D m from y)
  change σ.φ (Hb (Ideal.Quotient.mk _ x)) = _
  rw [hHb, hs']
  rfl

end GlobalTheory.CompanionTheory.DisoHm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformCokernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem grSum_induction {ι R : Type*} [CommRing R] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module R (A n)] {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} {hx : OperatorsCommute x}
    {C : GrSum hx → Prop} (m : GrSum hx) (h0 : C 0) (hof : ∀ n a, C (GrSum.of hx n a))
    (hadd : ∀ a b, C a → C b → C (a + b)) : C m :=
  DirectSum.induction_on (β := A) (motive := C) m h0 hof hadd

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}

namespace TowerAx

def mulKer (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) : T (e + 1) t S →ₗ[R] Ks p e t S :=
  LinearMap.codRestrict _ (r • LinearMap.id) fun y => by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := y))
    rw [← H.ker_eq e t S hS] at h
    exact (mem_Ks hS).2 h

@[simp]
theorem coe_mulKer (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty)
    (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (y : T (e + 1) t S) :
    (H.mulKer e t S hS r hr y : T (e + 1) t S) = r • y := rfl

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

def mulTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) : GrSum (hc (e + 1) S) →+ H.Tot hc S :=
  DirectSum.toAddMonoid fun t =>
    ((H.ops hc S).of e t).comp (H.mulKer e t S hS r hr).toAddMonoidHom

theorem mulTot_of (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (t : ℤ) (y : T (e + 1) t S) :
    H.mulTot hc e S hS r hr (GrSum.of (hc (e + 1) S) t y) =
      (H.ops hc S).of e t (H.mulKer e t S hS r hr y) :=
  DirectSum.toAddMonoid_of (β := fun t => T (e + 1) t S)
    (fun t => ((H.ops hc S).of e t).comp (H.mulKer e t S hS r hr).toAddMonoidHom) t y

theorem mulTot_X_smul (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (j : ι) (m : GrSum (hc (e + 1) S)) :
    H.mulTot hc e S hS r hr ((MvPolynomial.X j : MvPolynomial ι R) • m) =
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) •
        H.mulTot hc e S hS r hr m := by
  induction m using grSum_induction with
  | h0 => simp
  | hof t y =>
    rw [GrSum.X_smul_of, mulTot_of, mulTot_of, BiOps.X_smul_of]
    congr 1
    apply Subtype.ext
    change r • mm j (e + 1) t S y = mm j (e + 1) t S (r • y)
    rw [map_smul]
  | hadd a b ha hb => rw [smul_add, map_add, map_add, smul_add, ha, hb]

theorem mulTot_X_pow_smul (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty)
    (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (j : ι) (k : ℕ)
    (m : GrSum (hc (e + 1) S)) :
    H.mulTot hc e S hS r hr ((MvPolynomial.X j : MvPolynomial ι R) ^ k • m) =
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
        H.mulTot hc e S hS r hr m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, mulTot_X_smul, ih]

theorem mulKer_res (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (hS : S.Nonempty) (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (a : T (e + 1) t S) :
    H.mulKer e t S' (hS.mono h) r hr (res (e + 1) t S S' h a) =
      H.resK e t h (H.mulKer e t S hS r hr a) := by
  apply Subtype.ext
  rw [coe_resK, coe_mulKer, coe_mulKer, map_smul]

theorem exists_X_pow_smul_mem_range (H : TowerAx ρ res p mm)
    (hyp : ∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S),
      GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) =
        (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b)
    (S : Finset ι) (j : ι) (hS : S.Nonempty) (e : ℕ) (t : ℤ) (w : T (e + 1) t (insert j S))
    (hw : w ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t (insert j S)))) :
    ∃ (h : w ∈ Ks p e t (insert j S)) (k : ℕ),
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
          (H.ops hc (insert j S)).of e t ⟨w, h⟩ ∈
        LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  have hS' : (insert j S).Nonempty := Finset.insert_nonempty j S
  induction hw using Submodule.smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨k, t', a, hk⟩ := hyp (e + 1) S j t y hS
    refine ⟨(H.mulKer e t _ hS' r hr y).2, k, (H.ops hc S).of e t' (H.mulKer e t' S hS r hr a), ?_⟩
    have h1 := congrArg (H.mulTot hc e (insert j S) hS' r hr) hk
    rw [mulTot_X_pow_smul, mulTot_of, mulTot_of, mulKer_res H e t' (Finset.subset_insert j S) hS]
      at h1
    rw [resTot_of]
    exact h1
  | add x _ y _ hx hy =>
    obtain ⟨hx', k₁, hk₁⟩ := hx
    obtain ⟨hy', k₂, hk₂⟩ := hy
    refine ⟨add_mem hx' hy', k₁ + k₂, ?_⟩
    have hsum : (H.ops hc (insert j S)).of e t ⟨x + y, add_mem hx' hy'⟩ =
        (H.ops hc (insert j S)).of e t ⟨x, hx'⟩ + (H.ops hc (insert j S)).of e t ⟨y, hy'⟩ :=
      map_add ((H.ops hc (insert j S)).of e t) ⟨x, hx'⟩ ⟨y, hy'⟩
    rw [hsum, smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end TowerAx

end Tower

theorem tower_kernels_lift_after_X_pow : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → ∀ (S : Finset ι) (j : ι) (b : H.Tot hc (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • b ∈ LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  intro ι _ R _ g ρ T _ _ res p mm hc H hyp S j b hS
  have hS' : (insert j S).Nonempty := Finset.insert_nonempty j S
  induction b using (H.ops hc (insert j S)).induction with
  | h0 => exact ⟨0, by simp⟩
  | hof e t a =>
    have ha : (a : T (e + 1) t (insert j S)) ∈
        Ideal.span (Set.range ρ) ^ (e + 1) •
          (⊤ : Submodule R (T (e + 1) t (insert j S))) := by
      rw [← H.ker_eq e t _ hS']
      exact (mem_Ks hS').1 a.2
    obtain ⟨_, k, hk⟩ := H.exists_X_pow_smul_mem_range hc hyp S j hS e t a ha
    exact ⟨k, hk⟩
  | hadd x y hx hy =>
    obtain ⟨k₁, hk₁⟩ := hx
    obtain ⟨k₂, hk₂⟩ := hy
    refine ⟨k₁ + k₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_exhaustion_statement : PositivityTheory.RgDs.K.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.WordFam.exhaust | exact GlobalTheory.CompanionTheory.WordFam.exhaust | (intros; apply GlobalTheory.CompanionTheory.WordFam.exhaust <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicativeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_log_multiplicative : ∀ {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ),
    (∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) → ∀ v w : A, v - 1 ∈ J → w - 1 ∈ J →
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  first | exact @GlobalTheory.CompanionTheory.TruncLog.dlog_mul | exact GlobalTheory.CompanionTheory.TruncLog.dlog_mul | (intros; apply GlobalTheory.CompanionTheory.TruncLog.dlog_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousEpsilonPowerStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_epsilon_power : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : ((base l).cont ℤ_[l]).A,
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
  Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | exact GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | (intros; apply GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLiftStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_lift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  first | exact @GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | exact GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | (intros; apply GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWittStatement
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_acris_truncated_witt : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisFlat.flat_acr | exact GlobalTheory.CompanionTheory.CrisFlat.flat_acr | (intros; apply GlobalTheory.CompanionTheory.CrisFlat.flat_acr <;> assumption)
end

