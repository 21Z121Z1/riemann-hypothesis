import Mathlib

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.CosDens
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

def CosDens : Prop :=
  ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν m : Measure X) [IsFiniteMeasure m],
    IsFiniteMeasureOnCompacts ν →
    ∀ (H : ℕ → AddSubgroup X), (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      Antitone H → (∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) →
      ∀ (c0 : X) (κ : ENNReal), m {z | z - c0 ∈ H 0}ᶜ = 0 →
        (∀ n h, h - c0 ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n}) →
        ∀ S : Set X, IsCompact S → m S = κ * ν (S ∩ {z | z - c0 ∈ H 0})

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HenselCount
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

def HenselCount : Prop :=
  ∀ (V X : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), (∀ n, IsOpen (Λ n : Set V)) →
      (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ → (∀ n, IsOpen (H n : Set X)) →
      (∀ n, IsCompact (H n : Set X)) →
      ∀ D : V →+ X, (∀ n, (Λ n).map D = H n) →
      ∀ (G : V → X) (y : V),
        (∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
        ∀ n h, h - G y ∈ H 0 →
          μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) = μ (Λ 0) * ν (H n)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LBSubm
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter
open scoped ENNReal

def SubmLB : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) → ∀ W : Set (Fin n → ℝ), IsOpen W → x0 ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (f x0), ∀ S ⊆ N, MeasurableSet S →
        c * ν S ≤ μ (f ⁻¹' S ∩ W)

theorem submLB_holds : SubmLB := by
  intro n m μ ν hμ hν f hf x0 hx0 W hW hxW
  let A := fderiv ℝ f x0
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  let Θ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => T.symm (f x, (T x).2)
  have hΘc : ContDiff ℝ 1 Θ :=
    T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))
  have hfA : ∀ x, A (Θ x) = f x := by
    intro x
    rw [← hT1]; simp [Θ]
  have hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x :=
    fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt
  have hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    let P := (ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap
    have hP : HasFDerivAt (fun x => (T x).2) P x0 := P.hasFDerivAt
    have h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0 :=
      ((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP
    have h2 := T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1
    rw [show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from
      h2.fderiv]
    ext1 y
    change T.symm ((fderiv ℝ f x0) y, (T y).2) = y
    have : ((fderiv ℝ f x0) y, (T y).2) = T y := Prod.ext (hT1 y).symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  have hs : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have := hΘc.contDiffAt.hasStrictFDerivAt (x := x0) one_ne_zero
    rw [hid] at this
    exact this
  let PH := hs.toOpenPartialHomeomorph Θ

  have hO : IsOpen (PH.source ∩ W) := PH.open_source.inter hW
  have hxO : x0 ∈ PH.source ∩ W := ⟨hs.mem_toOpenPartialHomeomorph_source, hxW⟩
  obtain ⟨K0, hK0c, hxK0, hK0O⟩ := exists_compact_subset hO hxO

  have hDc : Continuous fun x => (fderiv ℝ Θ x).det :=
    ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)
  obtain ⟨Dm, hDm⟩ := hK0c.exists_bound_of_continuousOn hDc.continuousOn
  set D' : ℝ≥0∞ := ENNReal.ofReal (max Dm 1) with hD'
  have hD'0 : D' ≠ 0 := by
    rw [hD', Ne, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD'top : D' ≠ ⊤ := ENNReal.ofReal_ne_top

  let V0 := PH '' interior K0
  have hV0o : IsOpen V0 := PH.isOpen_image_of_subset_source isOpen_interior
    (interior_subset.trans (hK0O.trans inter_subset_left))
  have hΘx0 : Θ x0 ∈ V0 := ⟨x0, hxK0, rfl⟩

  have hTV : T '' V0 ∈ 𝓝 (T (Θ x0)) :=
    (T.toHomeomorph.isOpenMap _ hV0o).mem_nhds ⟨_, hΘx0, rfl⟩
  rw [nhds_prod_eq] at hTV
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.1 hTV
  let lam : Measure A.ker := Measure.addHaar
  set Bk := interior v with hBk
  have hBk0 : lam Bk ≠ 0 :=
    (isOpen_interior.measure_pos lam ⟨_, mem_interior_iff_mem_nhds.2 hv⟩).ne'
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c0, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    have := (isOpen_univ.measure_pos (μ.map T) univ_nonempty).ne'
    rw [hsm] at this
    exact this rfl
  refine ⟨min (D'⁻¹ * c0 * lam Bk) 1,
    lt_min (pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.2 hD'top) hc0) hBk0))
      one_pos,
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _), u, ?_, fun S hSu hSm => ?_⟩
  · have e : (T (Θ x0)).1 = f x0 := by rw [hT1, hfA]
    rw [← e]
    exact hu
  · let s := K0 ∩ Θ ⁻¹' (A ⁻¹' S)
    have hsm' : MeasurableSet s := hK0c.isClosed.measurableSet.inter
      ((A.continuous.comp hΘc.continuous).measurable hSm)
    have hs_sub : s ⊆ f ⁻¹' S ∩ W := fun x hx =>
      ⟨by show f x ∈ S; rw [← hfA]; exact hx.2, (hK0O hx.1).2⟩
    have hsrc : s ⊆ PH.source := fun x hx => (hK0O hx.1).1
    have hcv := lintegral_abs_det_fderiv_eq_addHaar_image μ hsm'
      (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hsrc)
    have hbound : μ (Θ '' s) ≤ D' * μ s := by
      rw [← hcv, ← setLIntegral_const]
      refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
      have h := hDm x hx.1
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    have hsub2 : T ⁻¹' (S ×ˢ Bk) ⊆ Θ '' s := by
      intro z hz
      obtain ⟨z', hz'V, hTz⟩ := huv ⟨hSu hz.1, interior_subset hz.2⟩
      have hzz : z' = z := T.injective hTz
      subst hzz
      obtain ⟨x, hxK, rfl⟩ := hz'V
      refine ⟨x, ⟨interior_subset hxK, ?_⟩, rfl⟩
      show A (Θ x) ∈ S
      rw [← hT1]
      exact hz.1
    have hmeasT : μ (T ⁻¹' (S ×ˢ Bk)) = c0 * (ν S * lam Bk) := by
      rw [← Measure.map_apply T.continuous.measurable (hSm.prod isOpen_interior.measurableSet),
        hsm, Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    calc min (D'⁻¹ * c0 * lam Bk) 1 * ν S ≤ D'⁻¹ * c0 * lam Bk * ν S :=
          mul_le_mul_left (min_le_left _ _) _
      _ = D'⁻¹ * μ (T ⁻¹' (S ×ˢ Bk)) := by rw [hmeasT]; ring
      _ ≤ D'⁻¹ * μ (Θ '' s) := mul_le_mul_right (measure_mono hsub2) _
      _ ≤ D'⁻¹ * (D' * μ s) := mul_le_mul_right hbound _
      _ = μ s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hD'0 hD'top, one_mul]
      _ ≤ μ (f ⁻¹' S ∩ W) := measure_mono hs_sub

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
section
noncomputable section

namespace PI.VolStabSW

def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)

def IsQuadInv (k K : Type) [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K) : Prop :=
  (∀ x, σ (σ x) = x) ∧
    ((IsField K ∧ Module.finrank k K = 2 ∧ σ ≠ AlgEquiv.refl) ∨
      ∃ e : K ≃ₐ[k] k × k, ∀ x, e (σ x) = (e x).swap)

def FFCount : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, ∀ (k K : Type) [Field k] [Finite k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K), IsQuadInv k K σ → (2 : k) ≠ 0 →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ a : ℕ, a + 2 ≤ M → ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) →
    IsUnit T.det →
    |(Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) /
        (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1| ≤ C * ((Nat.card k : ℝ)⁻¹) ^ 2

def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))

def FFInert : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl → (2 : k) ≠ 0 →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar
section
noncomputable section

open NumberField

namespace PI.VolStabSW

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnd χ hχ h1 x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let g : F →+ ℂ := AddMonoidHom.mk' (fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) /
    (2 * Real.pi * Complex.I)) (by intro a b; simp only [map_add, add_div])
  have hint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have he : Complex.exp (ℓ (algebraMap F (InfiniteAdeleRing F) a)) = 1 := by
      rw [← hℓ]
      exact h1 a ha
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨n, ?_⟩
    show ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = n
    rw [hn, mul_div_assoc, div_self hI, mul_one]
  have hg := hA F Λ hne hnd g hint
  have hzero : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h := hg a
    change ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = 0 at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hI
  have hdense : DenseRange (algebraMap F (InfiniteAdeleRing F)) := by
    first
      | exact InfiniteAdeleRing.denseRange_algebraMap F
      | exact InfiniteAdeleRing.denseRange_algebraMap
      | exact NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have hx : ℓ x = 0 :=
    hdense.induction_on x (isClosed_eq hℓc continuous_const) hzero
  rw [hℓ, hx, Complex.exp_zero]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoPolish
section
noncomputable section

namespace PI.VolStabSW.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  letI := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace

end PI.VolStabSW.TopoPolish
end
end

