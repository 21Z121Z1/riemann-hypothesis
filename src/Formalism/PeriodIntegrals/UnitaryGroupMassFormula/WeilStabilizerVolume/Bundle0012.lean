import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.SdUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfLoc
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology

def LinDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A →
      DensAll μ A id ν Set.univ

def ChangeVar : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)), μ.IsAddHaarMeasure →
    ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) →
      ∃ N, IsOpen N ∧ x0 ∈ N ∧ ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A ∧
        ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ N →
          ∃ G : (Fin n → ℝ) → ℝ, Continuous G ∧ HasCompactSupport G ∧
            ∀ S : Set (Fin m → ℝ), IsCompact S →
              ∫ v in f ⁻¹' S, φ v ∂μ = ∫ v in A ⁻¹' S, G v ∂μ

theorem submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by
  intro n m μ ν hμ hν f hf x0 hx0
  obtain ⟨N, hN, hxN, A, hA, hG⟩ := h2 n m μ hμ f hf x0 hx0
  refine ⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩
  obtain ⟨G, hGc, hGs, hGe⟩ := hG φ hc hs hφ
  obtain ⟨g, hgc, hg⟩ := h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)
  refine ⟨g, hgc, fun S hS => ?_⟩
  have := hg S hS
  simp only [Set.image_id] at this ⊢
  rw [hGe S hS, this]

theorem submDens_of_local (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx

theorem linDens_holds : LinDens := by
  intro n m μ ν hμ hν A hA φ hc hs _
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  let K := A.ker
  let lam : Measure K := Measure.addHaar
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let H : (Fin m → ℝ) × K → ℝ := fun w => φ (T.symm w)
  have hHc : Continuous H := hc.comp T.symm.continuous
  have hHs : HasCompactSupport H := hs.comp_homeomorph T.symm.toHomeomorph
  let s : Set K := Prod.snd '' tsupport H
  have hsc : IsCompact s := hHs.image continuous_snd
  let ψ : (Fin m → ℝ) → ℝ := fun y => ∫ k in s, H (y, k) ∂lam
  have hψc : Continuous ψ :=
    continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc
  have hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    apply image_eq_zero_of_notMem_tsupport
    intro h'
    exact hk ⟨(y, k), h', rfl⟩
  refine ⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  simp only [Set.image_id]
  let Q : (Fin m → ℝ) × K → ℝ := (Prod.fst ⁻¹' S).indicator H
  have hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v) := by
    intro v
    simp only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hQi : Integrable Q (ν.prod lam) :=
    (hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)
  rw [← integral_indicator (hSm.preimage A.continuous.measurable)]
  simp_rw [hQ]
  have e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T) := by
    rw [show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
    rfl
  rw [e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul,
    ← integral_indicator hSm, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · simp only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]
  · simp [Q, Set.indicator, hy]

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExOmTOfSteps
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem latSB_holds : LatSB := by
  intro F E _ _ _ _ d M n b v
  have : Module.Finite F E := Module.Finite.of_basis b
  exact PositiveNearLattice.isSB_latV b v n M

theorem exOmT_of_steps' (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hDI : DensFibInf)
    (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps hI hV latSB_holds hU hDI hDV hR

theorem exOmT_of_open (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps' hI hV hU densFibInf_holds densFibV_holds hR

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVolA
section
noncomputable section

namespace PI.VolStabW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_one_of_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) (hA : ann χ (L : Set V) = L) :
    μ (L : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hLo.measurableSet]
    exact integrableOn_const hfin.ne
  have h0 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0) := by
    funext y
    rw [hT y]
    by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]
  rw [e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h0
  have h1 : c * c = 1 := by exact_mod_cast h0
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c = 1 := by nlinarith
  rw [hc, measureReal_def, ENNReal.toReal_eq_one_iff] at hc1
  exact hc1

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq {V : Type} (ψ0 : Fv F v → ℂ) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y)
    (hD : {y | ∀ x ∈ L, B x y ∈ v.adicCompletionIntegers F} = L) :
    ann (fun x y => ψ0 (B x y)) L = L := by
  ext y
  constructor
  · intro hy
    rw [← hD]
    intro x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy
    rw [← hD] at hy
    intro x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

theorem ev_int (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) f ∈ (v.adicCompletionIntegers F) := by
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) f
  refine hfin.eventually_cofinite_notMem.mono fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v ((f : v.adicCompletion F)) = v.valuation F f :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  exact (this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)

theorem ev_int_all {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) :=
  Filter.eventually_all.2 fun i => ev_int (f i)

end Ann

end VolAAW

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdSt
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def RPAbs : Prop :=
  ∀ (ι : Type) [Countable ι] (W : ι → Type) [∀ i, MeasurableSpace (W i)]
    (m : ∀ i, Measure (W i)) [∀ i, SigmaFinite (m i)] (L : ∀ i, Set (W i)),
    (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ⊤) →
    (∀ S : Finset ι, ∃ c : ENNReal, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c) →
    ∃ ρ : Measure (∀ i, W i), SFinite ρ ∧
      ρ {x | ¬ ∀ᶠ i in Filter.cofinite, x i ∈ L i} = 0 ∧
      (∀ i (C : Set (W i)), MeasurableSet C → m i Cᶜ = 0 → ρ {x | x i ∉ C} = 0) ∧
      ∀ f : ∀ i, W i → ℂ, (∀ i, Integrable (f i) (m i)) →
        (∀ᶠ i in Filter.cofinite, f i = (L i).indicator 1) →
        Integrable (fun x => ∏ᶠ i, f i (x i)) ρ ∧
        HasProd (fun i => ∫ w, f i w ∂(m i)) (∫ x, ∏ᶠ i, f i (x i) ∂ρ)

def RPFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
      (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E)),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Ainf F) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
      (fib : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Fv F v) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Fv F v) σ (gramE σ J X0) hT))

def RPGlue : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M a d : ℕ) (b : Module.Basis (Fin d) F E),
  ∃ Γ : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) →
      (Fin a → Fin M → AF F ⊗[F] E),
    Measurable Γ ∧ ∀ p, (∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v) →
      projInf (Γ p) = p.1 ∧ ∀ v, projV v (projFin (Γ p)) = p.2 v

def RPGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
  MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} ∧
  MeasurableSet {X : Fin a → Fin M → Ainf F ⊗[F] E |
    gramR (Ainf F) σ J X = T.map (inclR (Ainf F))} ∧
  (∀ v : HeightOneSpectrum (𝓞 F), MeasurableSet {X : Fin a → Fin M → Fv F v ⊗[F] E |
    gramR (Fv F v) σ J X = T.map (inclR (Fv F v))}) ∧
  ∀ X : Fin a → Fin M → AF F ⊗[F] E, gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) →
    (∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) →
    gramR (AF F) σ J X = T.map (inclR (AF F))

def RPTail : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a →
      Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (d : ℕ) (b : Module.Basis (Fin d) F E),
    (∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) →
    (∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ →
      ∫ X, Φ X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} =>
        fibV v.1 (hermOf (Fv F v.1) σ (gramE σ J X0) hT) (latV b v.1)) c

def LatCofin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a M d d' : ℕ)
    (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E),
    ∀ᶠ v in Filter.cofinite, latV (M := M) (n := a) b v = latV b' v

theorem restrProd_of (hA : RPAbs) (hF : RPFib) (hG : RPGlue) (hGr : RPGram) (hTl : RPTail)
    (hL : LatCofin) : RestrProd := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμi νinf hνi μv hμv νv hνv
    fibInf hfi fibV hfv hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have cF := hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨hsfI, hintI⟩ := cF.1 μinf νinf fibInf hfi
  have hFv := fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)
  have hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    fun v Φ h => (hFv v).2 Φ h.1.continuous h.2
  let b := Module.finBasis F E
  rcases hTl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV _ b hSB (hmult _ b) with
    ⟨v0, hv0⟩ | hconv
  · refine ⟨0, by simp, fun d' b' Φ Φinf Φf Φv _ _ hp _ => ⟨integrable_zero_measure, ?_⟩⟩
    have h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0 :=
      hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩
    rw [integral_zero_measure, h0.tprod_eq, mul_zero]
  · let W : HeightOneSpectrum (𝓞 F) → Type := fun v => Fin a → Fin M → Fv F v ⊗[F] E
    let m : ∀ v, Measure (W v) := fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)
    have : ∀ v, SigmaFinite (m v) := fun v => (hFv v).1
    have := hsfI
    have hLm : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
    have hLf : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
      have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
      rw [integrable_indicator_iff (hLm v)] at h
      exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
    obtain ⟨ρ, hρsf, hρgood, hρmarg, hρint⟩ :=
      hA (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv
    have := hρsf
    obtain ⟨Γ, hΓm, hΓ⟩ := hG F E M a _ b
    have cG := hGr F E σ M J a (gramE σ J X0)
    let P : Measure ((Fin a → Fin M → Ainf F ⊗[F] E) × ∀ v, W v) :=
      (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)).prod ρ
    have hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0 := by
      rw [Measure.prod_prod, hρgood, mul_zero]
    refine ⟨P.map Γ, ?_, ?_⟩
    · rw [Measure.map_apply hΓm cG.1]
      have h1 : (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
          {y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) (hfi.1 _)
      have h2 : ∀ v, m v {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        fun v => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hfv v).1 _)
      have hbad : Γ ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} ⊆
          ({y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) ∪
            ⋃ v, Set.univ ×ˢ {x : ∀ v, W v | x v ∉
              {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}}) := by
        intro p hp
        by_contra hn
        have hi : gramR (Ainf F) σ J p.1 = (gramE σ J X0).map (inclR (Ainf F)) := by
          by_contra h; exact hn (Or.inl ⟨h, Set.mem_univ _⟩)
        have hg : ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
          by_contra h; exact hn (Or.inr (Or.inl ⟨Set.mem_univ _, h⟩))
        have hv : ∀ v, gramR (Fv F v) σ J (p.2 v) = (gramE σ J X0).map (inclR (Fv F v)) := by
          intro v; by_contra h
          exact hn (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_univ _, h⟩)))
        obtain ⟨e1, e2⟩ := hΓ p hg
        apply hp
        apply cG.2.2.2 (Γ p)
        · rw [e1]; exact hi
        · intro v; rw [e2 v]; exact hv v
      refine measure_mono_null hbad (measure_union_null ?_ (measure_union_null hgood
        (measure_iUnion_null fun v => ?_)))
      · rw [Measure.prod_prod, h1, zero_mul]
      · rw [Measure.prod_prod, hρmarg v _ (cG.2.2.1 v) (h2 v), mul_zero]
    · intro d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have hΦm : Measurable Φ :=
        TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      have hf : ∀ v, Integrable (Φv v) (m v) := fun v => hSB v _ (hp.1 v)
      have hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 :=
        (hp.2.1.and (hL F E a M d' _ b' b)).mono fun v h => h.1.trans (by rw [h.2])
      obtain ⟨hIρ, hHP⟩ := hρint Φv hf hfc
      have hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
        rw [ae_iff]
        exact measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood
      have hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v) := by
        filter_upwards [hae'] with p hp'
        obtain ⟨e1, e2⟩ := hΓ p hp'
        rw [hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]
        congr 1
        exact finprod_congr fun v => by rw [e2 v]
      have hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P :=
        (hintI Φinf hc1 hc2).mul_prod hIρ
      refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2
        (hPI.congr hae.symm), ?_⟩
      rw [integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae,
        integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)),
        ← hHP.tprod_eq]

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoClose
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem lcscPolish_holds : LCSCPolish := fun Y _ _ _ _ => TopoPolish.polish_of_lcsc Y

theorem secCtblW_holds : SecCtblW := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem scha_holds : SCHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem measGrp_holds : MeasGrp := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ⟨inferInstance, inferInstance⟩

end PI.VolStabW
end
end

