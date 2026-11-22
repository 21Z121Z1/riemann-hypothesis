import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataRows
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataForms
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0015
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0037

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CanonicalTranslateJets
section
theorem UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr :
    ∀ (D : Formalism.BasicNotions.D7),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ ({D.host.sqd} : Set D.host.E) :=
    (IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun y _ => Algebra.IsAlgebraic.isAlgebraic y).le hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by simpa using hy⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * D.host.d, a * e + b * c, by push_cast; linear_combination (b * e : D.host.E) * hs⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbeddingTypes
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.Reformulated.B.EmbeddingTypes.core {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ s ∈ nonZeroDivisors R, s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ y hy
  exact ⟨t, t.2, by simpa [Submonoid.smul_def] using ht⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt :
    ∀ (D : Formalism.BasicNotions.D7) (j : ℕ) (y : (D.sp.W j).V),
    ∃ s ∈ nonZeroDivisors (NumberField.RingOfIntegers D.host.E),
      s • y ∈
        (D.sp.W
            j).L0 := by
  intro D j y
  exact UpperTheory.Reformulated.B.EmbeddingTypes.core (K := D.host.E) _ (D.sp.W j).standardTuple_isLattice.span_eq_top y
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorThird
section
theorem UpperTheory.Reformulated.B.ExistsDenominatorThird.exists_den :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (x : ((D.fm u).lat (0 : ℕ)).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              (0 :
                ℕ)).L := by
  intro D u x
  have hx : x ∈ Submodule.span D.what₂.LL
      ((((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) := by
    rw [((D.fm u).lat_good 0).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIdealDenominator
section
theorem UpperTheory.Reformulated.B.ExistsIdealDenominator.exists_denI :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              i).L := by
  intro D u i x
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat i).L : Set ((D.fm u).lat i).V) := by
    rw [((D.fm u).lat_good i).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice
section
theorem UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  have hx : x ∈ Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherLast
section
theorem UpperTheory.Reformulated.B.Rd4.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  obtain ⟨⟨_, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers D.host.E) (nonZeroDivisors ℤ))
    D.host.E (Λ : Set (Fin n → D.host.E)) x (by rw [h.span_eq_top]; trivial)
  change algebraMap ℤ (NumberField.RingOfIntegers D.host.E) m • x ∈ _ at ht
  rw [Submodule.span_eq, algebraMap_smul] at ht
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.natAbs * m.natAbs, by positivity, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.natAbs_mul_self, mul_smul]
  exact zsmul_mem ht m
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerExtra
section
theorem UpperTheory.Reformulated.B.Gub1.proof.{u_1, u_2} :
    ∀ (E : Type u_1) (W : Type u_2) [inst : Field E] [inst_1 : NumberField E] [inst_2 : AddCommGroup W]
      [inst_3 : _root_.Module E W], GroundTheory.Heights₂.Heights.FiniteCovolume.LineIndexNeZero.Statement E W := by
  intro E W _ _ _ _ La x hL _ _
  have hfg : (La ⊓ (Submodule.span E {x}).toAddSubgroup).FG :=
    (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule _)).1
      (((Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule La)).2 hL.fg).of_le
        (AddSubgroup.toIntSubmodule.monotone inf_le_left))
  have := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine @AddSubgroup.index_ne_zero_of_finite _ _ _ (AddCommGroup.finite_of_fg_isAddTorsion _ ?_)
  rintro ⟨y, hy', hy⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨n, hn, hc⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
    (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨n, hn, (QuotientAddGroup.eq_zero_iff (n • _)).2 ?_⟩
  exact ⟨⟨n • c, hc⟩, smul_assoc n c x⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterionSecond
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be :
    Formalism.BasicNotions.D7 → ℂ :=
    fun (D : Formalism.BasicNotions.D7) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.aux2 :
    ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by
  exact ⟨le_rfl⟩

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc :
    Formalism.BasicNotions.D7 → ℂ → Prop :=
    fun (D : Formalism.BasicNotions.D7) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of :
    ∀ (D : Formalism.BasicNotions.D7) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hd : Nat.Prime D.host.d := D.host.hyp.2.1
  have hint : IsIntegral ℤ ((u : D.host.K) : D.host.E) :=
    (NumberField.RingOfIntegers.isIntegral_coe u).map (D.host.K.val.toRingHom.toIntAlgHom)
  obtain ⟨x, y, hxy, hz⟩ := UpperTheory.integral_imag_quadratic_half_int D.host.E D.host.d D.host.sqd hd.squarefree
    D.host.sqd_sq _ (u : D.host.K).2 hint
  have hs : D.host.φ₀ D.host.sqd = UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D := D.host.φ₀_mem
  refine ⟨x, y, hxy, ?_⟩
  rw [hz, map_div₀, map_add, map_mul, map_intCast, map_intCast, hs, map_ofNat]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticeVariant
section
theorem UpperTheory.Reformulated.B.LatticeVariant.lsd_spanDen :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)),
    Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) = ⊤ →
      ∀ (x : Fin n → D.host.E),
        ∃ (d : NumberField.RingOfIntegers D.host.E),
          d ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑d : D.host.E) • x ∈
              L := by
  intro D n L hL x
  have hx : x ∈ Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemInvCoe
section
theorem UpperTheory.Reformulated.B.Qf38.mem_inv_coe :
    ∀ (D : Formalism.BasicNotions.D7) {J : Ideal (NumberField.RingOfIntegers D.host.E)},
    J ≠ ⊥ →
      ∀ (x : D.host.E),
        x ∈ (↑J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E)⁻¹ ↔
          ∀ y ∈ J,
            ∃ (o : NumberField.RingOfIntegers D.host.E),
              (↑o : D.host.E) =
                x *
                  (↑y :
                    D.host.E) := by
  intro D J hJ x
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)]
  constructor
  · intro h y hy
    exact (FractionalIdeal.mem_one_iff _).mp
      (h _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩))
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    exact (FractionalIdeal.mem_one_iff _).mpr (h y hy)
end

