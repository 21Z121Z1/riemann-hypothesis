import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PMinusAnnihilatesLowestKTypeHolomorphicChamber
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.pMinus_kills_lowest : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), GlRel E → IsUnitary ε E → StrictAnti lam → IsHolChamber ε lam → IsMin ε E lam → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = lowK ε lam) → ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0 := by
  intro n ε V _ _ E lam hgl hu hanti hhol hmin L hL hLs hLh a b ha hb x hx
  by_contra hne
  have hkrel : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hkunit : KUnit ε E := fun a b hab x y => by
    rw [hu a b x y]; simp [Formalism.REAL.sgn, hab]
  let N : Submodule ℂ V := ⨆ p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}, L.map (E p.1.2 p.1.1)
  have hNfd : FiniteDimensional ℂ N := by infer_instance
  have hgen : ∀ p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}, ∀ y ∈ L, E p.1.2 p.1.1 y ∈ N :=
    fun p y hy => (le_iSup (fun p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false} => L.map (E p.1.2 p.1.1)) p)
      (Submodule.mem_map_of_mem hy)
  have hNs : KStab ε E N := by
    intro c d hcd v hv
    refine Submodule.iSup_induction _ (motive := fun v => E c d v ∈ N) hv ?_ ?_ ?_
    · intro p v hv
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
      have hc := hgl c d p.1.2 p.1.1
      have key : E c d (E p.1.2 p.1.1 y) = E p.1.2 p.1.1 (E c d y) +
          ((if d = p.1.2 then E c p.1.1 else 0) - (if p.1.1 = c then E p.1.2 d else 0)) y := by
        rw [← hc]; simp [Module.End.mul_apply]
      rw [key]
      refine N.add_mem (hgen p _ (hLs c d hcd y hy)) ?_
      rw [LinearMap.sub_apply]
      refine N.sub_mem ?_ ?_
      · split_ifs with h
        · exact hgen ⟨(p.1.1, c), p.2.1, by rw [hcd, h]; exact p.2.2⟩ y hy
        · simp
      · split_ifs with h
        · exact hgen ⟨(d, p.1.2), by rw [← hcd, ← h]; exact p.2.1, p.2.2⟩ y hy
        · simp
    · simp
    · intro u v hu hv; rw [map_add]; exact N.add_mem hu hv
  have hxN : E b a x ∈ N := hgen ⟨(a, b), ha, hb⟩ x hx
  have hN0 : N ≠ ⊥ := fun h => hne (by rw [h, Submodule.mem_bot] at hxN; exact hxN)
  obtain ⟨μ, w, hwN, hw0, hwh⟩ := GlobalTheory.T.exists_highest_vector_real_weight_unitary_compact n ε V E hkrel hkunit N hNfd hNs hN0
  have hex : ∃ p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}, ∃ y ∈ L, ⟪E p.1.2 p.1.1 y, w⟫_ℂ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have horth : ∀ v ∈ N, ⟪v, w⟫_ℂ = 0 := fun v hv =>
      Submodule.iSup_induction _ (motive := fun v => ⟪v, w⟫_ℂ = 0) hv
        (fun p v hv => by obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv; exact hcon p y hy)
        (by simp) (fun u v hu hv => by rw [inner_add_left, hu, hv, add_zero])
    exact hw0 (inner_self_eq_zero.1 (horth w hwN))
  obtain ⟨p, y, hy, hyw⟩ := hex
  have hyw' : ⟪y, ([(p.1.1, p.1.2)].map fun q : Fin n × Fin n => E q.1 q.2).prod w⟫_ℂ ≠ 0 := by
    have h1 := hu p.1.2 p.1.1 y w
    have hs : Formalism.REAL.sgn ε p.1.2 p.1.1 = -1 := by simp [Formalism.REAL.sgn, p.2.1, p.2.2]
    rw [hs] at h1
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    intro h0; apply hyw; rw [h1, h0]; simp
  obtain ⟨l', hl'len, hl'ε, hl'sum⟩ := GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε V E hgl hkunit L hL hLs (lowK ε lam) hLh μ w hwh
    true false [(p.1.1, p.1.2)] (by simp [p.2.1, p.2.2]) y hy hyw'
  obtain ⟨q, rfl⟩ := List.length_eq_one_iff.1 hl'len
  have hq := hl'ε q (by simp)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl'sum
  have hμ : μ = lowK ε lam - root q.1 q.2 := eq_sub_of_add_eq hl'sum
  have hlt := GlobalTheory.T.voganNormSq_lt_of_remove_noncompactRoot n ε lam hanti hhol q.1 q.2 hq.1 hq.2
  have hle := hmin μ w hw0 hwh
  rw [hμ] at hle
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))

theorem smoothOfRelativeDimension_str_of_cells (ho : ∀ w, IsOpenImmersion (cell a l w))
    (hc : ∀ x : Part a l, ∃ w, x ∈ Set.range (cell a l w)) :
    SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar a l)))
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Nat.card (CellVar a l))))
  let 𝒰 : (Part a l).OpenCover := Scheme.Cover.mkOfCovers (ι → Equiv.Perm (Fin N))
    (fun _ => Sp (MvPolynomial (CellVar a l) ℤ)) (cell a l) hc ho
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar a l))) 𝒰
    fun (w : ι → Equiv.Perm (Fin N)) => ?_
  change SmoothOfRelativeDimension _ (cell a l w ≫ _)
  rw [toZ_ext (cell a l w ≫ _) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (MvPolynomial (CellVar a l) ℤ))))]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card (CellVar a l)))).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2
    (Adelic.isStandardSmooth_mvPolynomial ℤ (CellVar a l))

theorem topologicalKrullDim_part_of_cells (ho : ∀ w, IsOpenImmersion (cell a l w))
    (hc : ∀ x : Part a l, ∃ w, x ∈ Set.range (cell a l w)) :
    topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) := by
  have hd : ∀ w, topologicalKrullDim (Set.range (cell a l w)) = (Nat.card (CellVar a l) + 1 : ℕ) := fun w => by
    have := ho w
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (cell a l w).isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := MvPolynomial (CellVar a l) ℤ)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [add_comm]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
    ((hd 1).ge.trans (topologicalKrullDim_subspace_le _ _))
  obtain ⟨w, hw⟩ := hc x
  have := ho w
  exact ⟨_, (cell a l w).isOpenEmbedding.isOpen_range, hw, (hd w).le⟩

theorem smooth_dim_isArithVar_part : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)),
    SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) ∧
      topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) ∧
      GlobalTheory.IsArithVar (str a l) (Nat.card (CellVar a l)) := fun ι κ _ _ N a l =>
  have ho := GlobalTheory.T.schubert_cell_open_immersion ι κ N a l
  have hc := GlobalTheory.T.flag_point_in_some_cell ι κ N a l
  ⟨smoothOfRelativeDimension_str_of_cells a l ho hc, topologicalKrullDim_part_of_cells a l ho hc,
    isArithVar_of_dim a l (topologicalKrullDim_part_of_cells a l ho hc)⟩

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoefIrrepHasDerivedAction
section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Matrix

namespace GlobalTheory.PsCo.PcEF.PolynomialCoefficientDerivedAction

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

lemma not_cdom {Λ : Fin n → ℝ} {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + Pi.single a 1 - Pi.single b 1) Λ := by
  rintro ⟨c, hc, he⟩
  let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
      map_add' := by
        intro f g
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        simp [Finset.mul_sum, mul_left_comm] }
  have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
    intro x
    simp [ψ, Pi.single_apply]
  have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
    abel
  rw [hl] at he
  have h := congrArg ψ he
  simp only [map_sum, map_smul, Formalism.REAL.root, map_sub, hψ, smul_eq_mul] at h
  have hr : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy := (hc x y h0).1
      have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

section Der

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : KG ε →* unitary (H →L[ℂ] H))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0)
  (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
  (hσ : ∀ g : KG ε, σ (toMK g) = ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))

include hder in

lemma conj (g : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Y * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Y * star (toMK g)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' g hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((g : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK g) :=
    toMK_inv' g
  have hγ' : ∀ t : ℝ, toMK (g * γ t * g⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
    intro t
    have e1 : toMK (g * γ t * g⁻¹) = toMK g * toMK (γ t) * toMK g⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  have h1 := hder _ hY' _ hγ'
  set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have h2 := (((ContinuousLinearMap.mul ℂ (H →L[ℂ] H) A).comp
      ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip (star A))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hder _ hY γ hγ)
  have hf : (fun t => ((τ (g * γ t * g⁻¹) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) =
      fun t => A * ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * star A := by
    funext t
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [hf] at h1
  have h3 := h2.unique (by simpa [Function.comp_def, mul_assoc] using h1)
  simpa [mul_assoc] using h3

include hder in

lemma conj_single (g : KG ε) {a b : Fin n} (hab : ε a = ε b) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ (Matrix.single a b 1) *
      star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Matrix.single a b 1 * star (toMK g)) := by
  rw [single_eq_kp a b]
  have e : toMK g * (kp1 a b + Complex.I • kp2 a b) * star (toMK g) =
      toMK g * kp1 a b * star (toMK g) + Complex.I • (toMK g * kp2 a b * star (toMK g)) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, map_add, map_smul, map_add, map_smul, ← conj τ dτ hder g (inK_hermitian_unit hab),
    ← conj τ dτ hder g (inK_skew_hermitian_unit hab), mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

include hder hσ in

lemma dτ_of_wt {μ : Fin n → ℝ} {v : H}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a : Fin n) :
    dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  set d : Fin n → ℂ := fun b => if b = a then Complex.I else 0 with hddef
  have hd : ∀ b, star (d b) = -d b := fun b => by
    simp only [d]; split_ifs <;> simp
  have hX := torep_inK_diag ε d hd
  set γ := onepCurve ε hX with hγdef
  have hD : ∀ t : ℝ, toMK (γ t) =
      Matrix.diagonal (fun b => Complex.exp (((if b = a then t else 0 : ℝ) : ℂ) * Complex.I)) := by
    intro t
    rw [toMK_onepCurve, ← Matrix.diagonal_smul, torep_exp_diag]
    congr 1
    funext b
    simp only [d, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hval : ∀ t : ℝ, ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v =
      Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := by
    intro t
    rw [← hσ, hD t, hv _ (by rw [← hD t]; exact (γ t).2)]
    have hs : (∑ b, μ b * (if b = a then t else 0)) = μ a * t := by
      simp [Finset.sum_ite_eq']
    rw [hs]
  have h1 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v)
      (dτ (Matrix.diagonal d) v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hder _ hX γ (toMK_onepCurve _ hX))
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v)
      (((μ a : ℂ) * Complex.I) • v) 0 := by
    rw [show (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) =
      fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v from funext hval]
    have h3 : HasDerivAt (fun t : ℝ => (((μ a * t : ℝ) : ℂ) * Complex.I)) ((μ a : ℂ) * Complex.I) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp).mul_const Complex.I
      simpa using this
    have := (h3.cexp).smul_const v
    simpa using this
  have heq := h1.unique h2
  have hdX : dτ (Matrix.diagonal d) = Complex.I • dτ (Matrix.single a a 1) := by
    rw [torep_diag_sum, Finset.sum_eq_single a (fun b _ hb => by simp [d, hb]) (by simp), map_smul]
    simp [d]
  rw [hdX, _root_.smul_apply, mul_comm, mul_smul] at heq
  exact smul_right_injective _ Complex.I_ne_zero heq

include hder hσ in

lemma hw {Λ : Fin n → ℝ}
    (hK5 : ∀ (μ : Fin n → ℝ) (v : H), v ∈ (⊤ : Submodule ℂ H) → v ≠ 0 →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v → Formalism.MainNotions.S.CDom ε μ Λ)
    {w : H} (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ Λ w) (a b : Fin n) (hab : a < b)
    (hε : ε a = ε b) : dτ (Matrix.single a b 1) w = 0 := by
  by_contra hx
  refine not_cdom hab (hK5 _ _ Submodule.mem_top hx ?_)
  intro θ hθ
  set g := torepK ε hθ
  set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have hk : σ (Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I))) = A := hσ g
  have hAA : star A * A = 1 := Unitary.coe_star_mul_self _
  have hwA : A w = Complex.exp (((∑ c, Λ c * θ c : ℝ) : ℂ) * Complex.I) • w := by
    rw [← hk]
    exact hw θ hθ
  have key : A * dτ (Matrix.single a b 1) = (A * dτ (Matrix.single a b 1) * star A) * A := by
    rw [mul_assoc (A * dτ (Matrix.single a b 1)), hAA, mul_one]
  rw [hk, show A (dτ (Matrix.single a b 1) w) = (A * dτ (Matrix.single a b 1)) w from rfl, key,
    show (A * dτ (Matrix.single a b 1) * star A * A) w = (A * dτ (Matrix.single a b 1) * star A) (A w) from rfl,
    conj_single τ dτ hder g hε, hwA,
    show toMK g = Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I)) from rfl, fh_diag_conj,
    map_smul, map_smul, _root_.smul_apply, smul_smul]
  congr 1
  have hs : (∑ c, (Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c * θ c) = (∑ c, Λ c * θ c) + θ a - θ b := by
    simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, ite_mul]
  have hst : star (Complex.exp ((θ b : ℂ) * Complex.I)) = Complex.exp (-((θ b : ℂ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [hs, hst, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Der

end GlobalTheory.PsCo.PcEF.PolynomialCoefficientDerivedAction

namespace GlobalTheory.PsCo.PcEF

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

theorem polyCoefIrrep_hasDerivedAction : ToKType := by
  intro n ε γ W _ _ _ T hT _
  obtain ⟨-, hU, hK⟩ := hT
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨τ, hτc, hτ⟩ := uRepHom n ε W T hU
  obtain ⟨dτ, hder⟩ := derivExists n ε W τ hτc
  have hσ : ∀ g : KG ε, T (toMK g) = ((τ g : unitary (W →L[ℂ] W)) : W →L[ℂ] W) := fun g => (hτ g).symm
  obtain ⟨v0, -, hv0, hwt0⟩ := hK.2.2.2.1
  have hn : ‖v0‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  set w : W := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hwdef
  have hwn : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T γ w := by
    intro θ hθ
    rw [hwdef, map_smul, hwt0 θ hθ, smul_comm]
  refine ⟨KType.mk (V := W) τ hτc ?_ dτ hder w hwn
    (fun a => PolynomialCoefficientDerivedAction.dτ_of_wt τ dτ hder T hσ hwt a)
    (fun a b hab he => PolynomialCoefficientDerivedAction.hw τ dτ hder T hσ hK.2.2.2.2 hwt a b hab he), fun k => ?_⟩
  · intro S hS
    refine hK.2.2.1 S le_top (fun g hg v hv => ?_)
    have h := hS (torepK ε hg) v hv
    rw [← hσ] at h
    exact h
  · show LinearMap.trace ℂ W ((((τ k : unitary (W →L[ℂ] W)) : W →L[ℂ] W)) : W →ₗ[ℂ] W) = trK T (toMK k)
    rw [← hσ]
    rfl

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStableStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLat.Lv.level_iff | exact GlobalTheory.TwLat.Lv.level_iff | (intros; apply GlobalTheory.TwLat.Lv.level_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) := by
  first | exact @GlobalTheory.FiveClauseParts.parts_conj_five | exact GlobalTheory.FiveClauseParts.parts_conj_five | (intros; apply GlobalTheory.FiveClauseParts.parts_conj_five <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPairStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  first | exact @GlobalTheory.KapLat.fits_prod | exact GlobalTheory.KapLat.fits_prod | (intros; apply GlobalTheory.KapLat.fits_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFormulaSqrtNormalizedAbsValuesCMFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 → (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧ (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  first | exact @GlobalTheory.ProdForm.absHalf_prodFormula | exact GlobalTheory.ProdForm.absHalf_prodFormula | (intros; apply GlobalTheory.ProdForm.absHalf_prodFormula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeveStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S (KL n) : Set (finU E n)) ∧ IsCompact (globLev S (KL n) : Set (finU E n)) ∧ IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  first | exact @GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | exact GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | (intros; apply GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropZStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.PropZRow

theorem propZ : PropZ := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hs
  obtain ⟨hI, hN, hP, hF, hC, hL, ht⟩ := hD
  haveI := hI
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace f).mp inferInstance
  have hD : Hyp f D := ⟨hI, hN, hP, hF, hC, hL, ht⟩
  obtain ⟨τ, hτ, hU, hPow⟩ := GlobalTheory.T.exists_ratSec_unit_generic_fibre O ϖ hϖ Z f D hF hL sig hs
  obtain ⟨hg, hz⟩ := GlobalTheory.T.flat_scheme_special_fibre_nonempty O ϖ hϖ Z f hF (hC.toNonempty)
  obtain ⟨M, n, x₀, hM, hx₀, hreg, hunit⟩ := GlobalTheory.T.exists_power_section_special_fibre Z hN _ hg hz D τ hL hτ hU
  obtain ⟨gen, hgen, heq⟩ := GlobalTheory.T.regular_section_extends_over_fibre O ϖ hϖ Z f D hD hg (GlobalTheory.T.reduced_special_fibre_global_field O Z f hP hC) (GlobalTheory.T.regular_of_regular_at_codim_one Z hN) τ hτ hU M n x₀ hM hx₀ hreg hunit
  exact ⟨M, n, hM, ⟨gen, hgen, hPow M n gen heq⟩, GlobalTheory.T.valuation_constant_of_power_eq O ϖ hϖ Z f D hL sig hs M n gen hM hgen (hPow M n gen heq)⟩

end GlobalTheory.PropZRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImage
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb

theorem pullLat_mul_eq_mulLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  intro E _ _ _ w K B n ψ h g a ha
  have hinv : ∀ z, ψ (((a⁻¹ : B.Aˣ) : B.A) * z) = (h⁻¹ : GLw n w).val *ᵥ ψ z := by
    intro z
    have h1 := ha (((a⁻¹ : B.Aˣ) : B.A) * z)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec]
    have : ((h⁻¹ : GLw n w).val * h.val) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
  have key : ∀ y, y ∈ pullLat w B ψ (h * g) ↔ ((a⁻¹ : B.Aˣ) : B.A) * y ∈ pullLat w B ψ g := by
    intro y
    show (∀ (c : K.O) (i : Fin n), (((h * g)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
      (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y))) i ∈
        w.adicCompletionIntegers E)
    have e1 : ∀ c : K.O, ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y)) = (h⁻¹ : GLw n w).val *ᵥ ψ (c • y) := by
      intro c
      rw [← hinv, Algebra.mul_smul_comm]
    have e2 : ((h * g)⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * (h⁻¹ : GLw n w).val := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    simp only [e1, e2, Matrix.mulVec_mulVec]
  ext y
  constructor
  · intro hy
    refine ⟨((a⁻¹ : B.Aˣ) : B.A) * y, (key y).1 hy, ?_⟩
    show (a : B.A) * (((a⁻¹ : B.Aˣ) : B.A) * y) = y
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨z, hz, rfl⟩
    rw [key]
    show ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * z) ∈ pullLat w B ψ g
    rw [← mul_assoc, Units.inv_mul, one_mul]
    exact hz

end GlobalTheory.KapOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalIsometry_vacuumScalar_gaussSum_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) → Integrable (gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ))) volume → ∀ κ : ℂ, (∀ f : thetaSub ψ S T, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x, (f : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x) = κ * ((sumOp (opF hψ.1 S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) f : thetaSub ψ S T) : WO S T → ℂ) x) → ∀ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E), (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) → (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) → ∃ r : ℝ, 0 < r ∧ (∑ k, gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * t k * a - t k)) (t k)) * ∫ v, gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = r * κ := by
  first | exact @GlobalTheory.RatTrace.gauss_mul_integral | exact GlobalTheory.RatTrace.gauss_mul_integral | (intros; apply GlobalTheory.RatTrace.gauss_mul_integral <;> assumption)
end

