import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsResidualRepRestrictionOfLatticeShape
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

theorem UpperTheory.exists_residualRep_restriction_of_latticeShape :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Ok a → ∀ s : PD Unit (G ℚ Ω) k, LatShape D T.pr (resQ T.F T.g0) a s →
          ∃ s' : PD T.ι (G T.F Ω) k, (T.fr ∅).IsRes a s' ∧ T.OverQ s s' := by
  intro Ω _ _ _ l hl c D hD T hF k _ a _ _ P hS
  have hOk : T.Ok := hF.1
  have hP := hS.res.pair
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (a (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit (P.r x i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  have sh := fun v : T.ι => Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hP.low ()) hS.flag
  choose n hn hb using fun v : T.ι => Rq.luG k _ (P.r (g v)) (P.n ()) (hν (g v)) (hP.mult (g v)) (hP.low ())
    (sh v).1.1 (sh v).1.2
  let Q : PD T.ι (G T.F Ω) k := ⟨P.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj (Q.n v) * Q.r s * Q.n v) ∧
      ∀ i, Q.ψ v i s = P.ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ (P.r (g v)) (P.r ((g v)⁻¹ * resQ T.F s * g v)) (P.r (resQ T.F s)) _ _
      (hν (g v)) (hP.mult (g v)) (hP.low ()) (hn v) (hb v)
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hch : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), ∀ i, Q.ψ v i s = a (chi D T.pr i (resQ T.F s)) := fun v s hs i => by
    rw [(key v s hs).2, ← hconj (chi D T.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  refine ⟨Q, ⟨⟨fun x => hP.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ P.r hP.kill, hP.nrm, hn,
    fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩,
    ⟨fun x i => hS.res.res.diag (resQ T.F x) i, hch, Or.inl ⟨fun x => hS.supp _, fun v => (sh v).2 _ (hn v) (hb v)⟩⟩,
    fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, rfl, fun v => ⟨(), g v, hg v, hb v⟩⟩
  refine (hch v s hs.1 i).trans ?_
  rw [chi, Rq.muPs D hD T hOk _ s hs, Units.val_one, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepsIntegralMemClosedSubmodule
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem inner_eq_setIntegral_of_ae (w v : Lp ℂ 2 (quotientMeasure Γ μ)) {g : G → ℂ}
    (h : ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = g y) :
    inner ℂ w v = ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * g y ∂μ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

private theorem closed_stable [IsFiniteMeasure (quotientMeasure Γ μ)]
    (τ : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))) (hτ : IsClosed (τ : Set (Lp ℂ 2 (quotientMeasure Γ μ))))
    (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G → ℂ)
    (hc : Continuous (fun p : U × G => Ψ p.1 p.2)) (hb : ∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C)
    (hinv : ∀ u, ∀ γ ∈ Γ, ∀ m, Ψ u (γ * m) = Ψ u m)
    (hrep : ∀ u, ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = Ψ u y) :
    ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = ∫ u, Ψ u y ∂lam := by
  obtain ⟨C, hC⟩ := hb
  choose v hvτ hvr using hrep
  let Φ : G → ℂ := fun m => ∫ u, Ψ u m ∂lam
  have hΦc : Continuous Φ := by
    refine continuous_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
    · intro m
      exact (hc.comp (by fun_prop : Continuous fun u : U => (u, m))).aestronglyMeasurable
    · intro m
      exact Eventually.of_forall fun u => hC u m
    · exact Eventually.of_forall fun u => hc.comp (by fun_prop : Continuous fun m => (u, m))
  have hΦb : ∀ m, ‖Φ m‖ ≤ C * lam.real univ := fun m =>
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun u => hC u m)
  let f : RightCosetSpace Γ → ℂ := Quotient.lift Φ (by
    rintro a b ⟨γ, rfl⟩
    change Φ ((γ : G) * b) = Φ b
    simp only [Φ, hinv _ _ γ.2])
  have hfc : Continuous f :=
    (isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 hΦc
  have hf2 : MemLp f 2 (quotientMeasure Γ μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable (C * lam.real univ) (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ q
      exact hΦb y)
  have hrepΦ : ∀ᵐ y ∂μ, ((hf2.toLp f : Lp ℂ 2 (quotientMeasure Γ μ)) : RightCosetSpace Γ → ℂ) (mk Γ y) = Φ y := by
    have h := (quasiMeasurePreserving_mk Γ μ).ae (MemLp.coeFn_toLp hf2)
    filter_upwards [h] with y hy
    rw [hy]
    rfl
  refine ⟨hf2.toLp f, ?_, hrepΦ⟩
  haveI : CompleteSpace τ := hτ.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal τ, Submodule.mem_orthogonal]
  intro w hw
  rw [inner_eq_setIntegral_of_ae Γ μ w _ hrepΦ]
  have hw1 : Integrable (fun y => w (mk Γ y)) (μ.restrict (fundamentalDomain Γ)) := by
    have h1 : Integrable w (quotientMeasure Γ μ) :=
      (Lp.memLp w).integrable (by norm_num)
    exact Integrable.comp_measurable h1 (measurable_mk Γ)
  have hwm : StronglyMeasurable (fun y => w (mk Γ y)) := stronglyMeasurable_lift Γ μ w
  have hint : Integrable (Function.uncurry fun (u : U) (y : G) =>
      conj (w (mk Γ y)) * Ψ u y) (lam.prod (μ.restrict (fundamentalDomain Γ))) := by
    refine Integrable.mono' ((hw1.norm.mul_const C).comp_snd lam) ?_ ?_
    · have h1 : StronglyMeasurable (fun p : U × G => conj (w (mk Γ p.2))) :=
        continuous_star.comp_stronglyMeasurable (hwm.comp_measurable measurable_snd)
      exact h1.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC p.1 p.2) (norm_nonneg _)
  calc ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Φ y ∂μ
      = ∫ y in fundamentalDomain Γ, ∫ u, conj (w (mk Γ y)) * Ψ u y ∂lam ∂μ := by
        simp only [Φ, integral_const_mul]
    _ = ∫ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ ∂lam :=
        (integral_integral_swap hint).symm
    _ = 0 := by
        have h0 : ∀ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ = 0 := by
          intro u
          rw [← inner_eq_setIntegral_of_ae Γ μ w (v u) (hvr u)]
          exact Submodule.inner_left_of_mem_orthogonal (hvτ u) hw
        simp [h0]

end Gen

theorem UpperTheory.reps_integral_mem_closed_submodule :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)), IsClosed (τ : Set (L2 μ)) →
      ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G1 K n → ℂ),
        Continuous (fun p : U × G1 K n => Ψ p.1 p.2) → (∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C) → (∀ u, ∀ γ ∈ Gam K n, ∀ m, Ψ u (γ * m) = Ψ u m) → (∀ u, ∃ v ∈ τ, Reps μ v (Ψ u)) →
        ∃ v ∈ τ, Reps μ v fun m => ∫ u, Ψ u m ∂lam := by
  intro K _ _ n μ _ τ hτ U _ _ _ _ lam _ Ψ hc hb hinv hrep
  haveI : IsFiniteMeasure (quotientMeasure (Gam K n) μ) :=
    isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact closed_stable (Gam K n) μ τ hτ U lam Ψ hc hb hinv hrep
end

