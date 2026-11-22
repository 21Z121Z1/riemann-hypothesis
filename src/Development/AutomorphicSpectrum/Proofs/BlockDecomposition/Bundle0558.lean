import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.Bundle0001
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUnique
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.ArtinUniq

variable {K : Type} [Field K] [NumberField K]

theorem exists_ideal_unramified (L : Type) [Field L] [NumberField L] [Algebra K L] :
    ∃ 𝔡 : Ideal (𝓞 K), 𝔡 ≠ ⊥ ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔡 → IsUnramifiedIn K v L := by
  refine ⟨(differentIdeal (𝓞 K) (𝓞 L)).under (𝓞 K), ?_, fun v hv Q hQ hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ Q ∣ differentIdeal (𝓞 K) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

theorem mem_of_units_of_unif (v : HeightOneSpectrum (𝓞 K)) (M : Subgroup (v.adicCompletion K)ˣ)
    (hu : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = 1 → x ∈ M)
    (π : (v.adicCompletion K)ˣ) (hπ : IsUniformiserAt K v (π : v.adicCompletion K)) (hM : π ∈ M)
    (x : (v.adicCompletion K)ˣ) : x ∈ M := by
  have key : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) ≤ 1 → x ∈ M := by
    intro x hx
    obtain ⟨hπ1, hirr⟩ := hπ
    have hxm : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := hx
    have hx0 : (⟨x, hxm⟩ : v.adicCompletionIntegers K) ≠ 0 := fun h0 =>
      x.ne_zero (congrArg Subtype.val h0)
    obtain ⟨n, u, e⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
    have e' : (x : v.adicCompletion K) =
        ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * (π : v.adicCompletion K) ^ n :=
      congrArg Subtype.val e
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ 1 := ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) = 1 := by
      rw [← map_mul]
      have : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
          (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
          v.adicCompletion K) = 1 := congrArg Subtype.val u.mul_inv
      rw [this, map_one]
    have h4 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
      le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)
    have hy : x * (π ^ n)⁻¹ ∈ M := by
      refine hu _ ?_
      have : ((x * (π ^ n)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((u : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        rw [Units.val_mul, e', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        exact mul_inv_cancel_right₀ (pow_ne_zero n π.ne_zero) _
      rw [this, h4]
    have := M.mul_mem hy (M.pow_mem hM n)
    rwa [inv_mul_cancel_right] at this
  rcases le_total (Valued.v (x : v.adicCompletion K)) 1 with h | h
  · exact key x h
  · refine inv_mem_iff.1 (key x⁻¹ ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ h

theorem localIdele_eq {Art Art' : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K}
    (hA : IsGlobalArtinMap K Art) (hA' : IsGlobalArtinMap K Art')
    (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsUnramifiedIn K v L) (x : (v.adicCompletion K)ˣ) :
    abRestrict K L h (Art (QuotientGroup.mk (localIdele K v x))) =
      abRestrict K L h (Art' (QuotientGroup.mk (localIdele K v x))) := by
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  obtain ⟨π, hπ⟩ := exists_isUniformiserAt K v
  obtain ⟨Q, hQ, hQv⟩ := ReciprocityTheory.DiscreteGroups.GlobalClassField.exists_liesOver (K := K) L v
  refine mem_of_units_of_unif v (MonoidHom.eqLocus (localComposite K Art L h v)
    (localComposite K Art' L h v)) (fun y hy => ?_) π hπ ?_ x
  · have hy' : Valued.v ((localIdele K v y : AdeleRing (𝓞 K) K).2 v) = 1 := by
      rw [localIdele_snd_self]
      exact hy
    exact ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').trans
      ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').symm
  · have hπ' : IsUniformiserAt K v ((localIdele K v π : AdeleRing (𝓞 K) K).2 v) := by
      rw [localIdele_snd_self]
      exact hπ
    exact ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_unique v Q hv _ _
      ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)
      ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)

def infI : (InfiniteAdeleRing K)ˣ →* Ideles K :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _)

theorem inf_mem [IsTotallyComplex K] (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m)
    (hpow : ∀ x : Ideles K, x ^ m ∈ N) (y : (InfiniteAdeleRing K)ˣ) :
    infI y ∈ N := by
  haveI : ∀ w : InfinitePlace K, IsAlgClosed w.Completion := fun w =>
    IsAlgClosed.of_ringEquiv ℂ _
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm
  choose r hr using fun w : InfinitePlace K =>
    IsAlgClosed.exists_pow_nat_eq ((y : InfiniteAdeleRing K) w) hm
  obtain ⟨r', hb⟩ : ∃ r' : InfiniteAdeleRing K, r' ^ m = (y : InfiniteAdeleRing K) :=
    ⟨r, funext hr⟩
  obtain ⟨z, rfl⟩ : IsUnit r' := (isUnit_pow_iff hm.ne').1 (hb ▸ y.isUnit)
  have e : z ^ m = y := Units.ext (by rw [Units.val_pow_eq_pow_val, hb])
  rw [← e, map_pow]
  exact hpow _

theorem valued_le_of_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) {x : 𝓞 K}
    (hx : x ∈ v.asIdeal ^ n) :
    Valued.v (algebraMap K (v.adicCompletion K) (x : K)) ≤ WithZero.exp (-(n : ℤ)) := by
  have e2 : algebraMap K (v.adicCompletion K) (x : K) =
      ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x n).2 hx

theorem exists_modulus (𝔡 : Ideal (𝓞 K)) (h𝔡 : 𝔡 ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) : ∃ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ ∧ 𝔡 ∣ 𝔮 ∧ ∀ v ∈ S, 𝔮 ≤ v.asIdeal ^ n := by
  refine ⟨𝔡 * ∏ v ∈ S, v.asIdeal ^ n,
    mul_ne_zero h𝔡 (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero n v.ne_bot),
    dvd_mul_right _ _, fun v hv => ?_⟩
  exact Ideal.le_of_dvd ((Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) =>
    v.asIdeal ^ n) hv).mul_left _)

theorem abRestrict_eq : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (Art Art' : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K),
    IsGlobalArtinMap K Art → IsGlobalArtinMap K Art' →
    ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (c : IdeleClassGroup K),
      abRestrict K L h (Art c) = abRestrict K L h (Art' c) := by
  intro K _ _ _ Art Art' hA hA' L h c
  haveI := h.finiteDimensional
  haveI := h.isGalois
  haveI : NumberField L := NumberField.of_module_finite K L
  let f : Ideles K →* (L ≃ₐ[K] L) :=
    (abRestrict K L h).comp (Art.comp (QuotientGroup.mk' (diagUnits K).range))
  let f' : Ideles K →* (L ≃ₐ[K] L) :=
    (abRestrict K L h).comp (Art'.comp (QuotientGroup.mk' (diagUnits K).range))
  let N : Subgroup (Ideles K) := MonoidHom.eqLocus f f'
  have hfib : ∀ (B : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K),
      Continuous B → ∀ τ : L ≃ₐ[K] L,
      IsOpen {a : Ideles K | abRestrict K L h (B (QuotientGroup.mk a)) = τ} := fun B hB τ =>
    (ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber h τ).preimage (hB.comp continuous_quot_mk)
  have hopen : IsOpen (N : Set (Ideles K)) := by
    have e : (N : Set (Ideles K)) = ⋃ τ : L ≃ₐ[K] L,
        {a : Ideles K | abRestrict K L h (Art (QuotientGroup.mk a)) = τ} ∩
        {a : Ideles K | abRestrict K L h (Art' (QuotientGroup.mk a)) = τ} := by
      ext a
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ha => ⟨_, rfl, ha.symm⟩, fun ⟨τ, h1, h2⟩ => h1.trans h2.symm⟩
    rw [e]
    exact isOpen_iUnion fun τ => (hfib Art hA.1 τ).inter (hfib Art' hA'.1 τ)
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_unramified (K := K) L
  obtain ⟨S, n, hS⟩ := PI.AlgValsFin.W.exists_nbhd (N : Set (Ideles K)) hopen N.one_mem
  obtain ⟨𝔮, h𝔮, hd𝔮, hS𝔮⟩ := exists_modulus 𝔡 h𝔡 S n
  have hpow : ∀ x : Ideles K, x ^ Nat.card (L ≃ₐ[K] L) ∈ N := fun x => by
    show f _ = f' _
    rw [map_pow, map_pow, pow_card_eq_one', pow_card_eq_one']
  have hray : ∀ u ∈ rayUnits K 𝔮 {w | w.IsReal}, u ∈ N := by
    rintro u ⟨-, hu⟩
    have e : u = infI
        (Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _) u) *
        GlobalTheory.Mem.Chr.finPartI K u :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e]
    refine N.mul_mem (inf_mem N _ Nat.card_pos hpow _) (hS _ ⟨rfl, fun v => (hu v).1⟩ fun v hv => ?_)
    obtain ⟨-, x, hx, hle⟩ := hu v
    exact hle.trans (valued_le_of_mem v n (hS𝔮 v hv hx))
  have hloc : Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K))
      (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧
        IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π} ≤ N := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, π, hv, -, rfl⟩
    exact localIdele_eq hA hA' L h v (hun v fun hd => hv (hd.trans hd𝔮)) π
  have hdiag : (diagUnits K).range ≤ N := by
    rintro _ ⟨k, rfl⟩
    have e : QuotientGroup.mk' (diagUnits K).range (diagUnits K k) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨k, rfl⟩
    show abRestrict K L h (Art (QuotientGroup.mk' (diagUnits K).range (diagUnits K k))) =
      abRestrict K L h (Art' (QuotientGroup.mk' (diagUnits K).range (diagUnits K k)))
    simp only [e, map_one]
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨k, u, hu, b, hb, e⟩ := GlobalTheory.RayGen.exists_diag_mul_ray_mul_unif K 𝔮 h𝔮 a
  have ha : a ∈ N := e ▸ N.mul_mem (N.mul_mem (hdiag ⟨k, rfl⟩) (hray u hu)) (hloc hb)
  exact ha

end GlobalTheory.CompanionTheory.ArtinUniq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Summand

variable {D : D7}

theorem trace_inner_join (V : HSp D) {r s : ℕ} (x₁ y₁ : Mx D V.rank r) (x₂ y₂ : Mx D V.rank s) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (colJoin x₁ x₂) (colJoin y₁ y₂)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x₁ y₁) + Matrix.trace (GlobalTheory.StdUnn.inner V x₂ y₂) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]

theorem trace_inner_mul (V : HSp D) {n : ℕ} (U W : Mx D V.rank n) (A A' : Mx D n n)
    (h : HMul.hMul A' (adj A) = (1 : Mx D n n)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A')) = Matrix.trace (GlobalTheory.StdUnn.inner V U W) := by
  have e : GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A') =
      HMul.hMul (adj A) (HMul.hMul (GlobalTheory.StdUnn.inner V U W) A') := by
    simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

theorem inner_neg_left (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (-x) y = -GlobalTheory.StdUnn.inner V x y := by
  have : adj (-x) = -adj x := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (-y) = -GlobalTheory.StdUnn.inner V x y := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem inner_sub_left (V : HSp D) {n : ℕ} (x x' y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (x - x') y = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x' y := by
  have : adj (x - x') = adj x - adj x' := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.sub_mul]

theorem inner_sub_right (V : HSp D) {n : ℕ} (x y y' : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (y - y') = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x y' := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_sub]

theorem inner_zero_left (V : HSp D) {n : ℕ} (y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
  have : adj (0 : Mx D V.rank n) = 0 := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.zero_mul]

theorem inner_mul_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) :
    GlobalTheory.StdUnn.inner V x (HMul.hMul y B) = HMul.hMul (GlobalTheory.StdUnn.inner V x y) B := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_adj {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  simp [Matrix.trace, adj, map_sum]

theorem adj_inner (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V x y) = GlobalTheory.StdUnn.inner V y x := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) (hB : adj B = B) :
    Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y x) B) =
      cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V x y) B)) := by
  rw [← trace_adj, adj_mul, adj_inner, hB, Matrix.trace_mul_comm]

theorem exp_ring {R : Type*} [CommRing R] (c t₁ t₃ t₄ t₅ : R) (h : c + c = 1) :
    -t₁ + t₅ + c * t₃ + c * t₄ = t₅ + c * (t₃ - t₁ - t₁ + t₄) := by
  linear_combination t₁ * h

theorem sub_group {G : Type*} [AddCommGroup G] (a b c d : G) : a - b - (c - d) = a - b - c + d := by
  abel

theorem halfTr_eq (z : AE D) : halfTr z = algebraMap D.host.F (AF D.host.F) (1 / 2) * trA z := rfl

theorem half_add_half : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_add, add_halves, map_one]

theorem psi_halfTr_incA (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (e : D.host.E) :
    ψ (halfTr (incA D e)) = 1 := by
  have : halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
    have h : Algebra.trace (AF D.host.F) (AE D) (incA D e) =
        algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
      show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    rw [halfTr_eq, map_mul, trA, h]
  rw [this]
  exact hψ.2.2.1 _

theorem trace_inner_rat (V : HSp D) {n : ℕ} (p : Matrix (Fin V.rank) (Fin n) D.host.E) (b : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ e : D.host.E, Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) = incA D e := by
  refine ⟨Matrix.trace (pᴴ * (HSpace.gram V * p) * b), ?_⟩
  have : HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b) = rat (pᴴ * (HSpace.gram V * p) * b) := by
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [this]
  simp only [Matrix.trace, Matrix.diag_apply, rat, Matrix.map_apply, map_sum]

theorem psi_combine (ψ : AddChar (AF D.host.F) ℂ) (X Y T t₁ t₃ t₄ t₅ : AE D) (e₁ : X = -t₁ + t₅) (e₂ : Y = t₃)
    (e₃ : T = t₃ - cA D t₁ - t₁ + t₄) (e₄ : ψ (halfTr t₄) = 1) :
    ψ (trA X + halfTr Y) = ψ (trA t₅) * ψ (halfTr T) := by
  subst e₁ e₂ e₃
  have h : trA (-t₁ + t₅) + halfTr Y + halfTr t₄ = trA t₅ + halfTr (Y - cA D t₁ - t₁ + t₄) := by
    simp only [halfTr_eq, trA, map_add, map_sub, map_neg, GlobalTheory.DualPairCheck.trace_cA]
    exact exp_ring _ _ _ _ _ half_add_half
  rw [← AddChar.map_add_eq_mul, ← h, AddChar.map_add_eq_mul ψ _ (halfTr t₄), e₄, mul_one]

theorem summand (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (hb : (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (ha : IsUnit a.det)
    (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s)))
    (hx : xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a))
    (hy : yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹))
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E) :
    Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  have hunit : IsUnit (aᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  have hA : HMul.hMul (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) (adj (rat a)) = (1 : Mx D (r + s) (r + s)) := by
    have : cT (D.sp.cm.sig : D.host.E →+* D.host.E) a = aᴴ := rfl
    rw [this, ← rat_conjTranspose, ← rat_mul, Matrix.nonsing_inv_mul _ hunit, rat_one]
  have hB : adj (rat b) = rat b := by
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hz : rat (colJoin p q * a) = HMul.hMul (colJoin (rat p) (rat q)) (rat a) := by
    rw [rat_mul, rat_colJoin]
  have hzx : rat (colJoin p q * a) + xPart v = HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a) := by
    rw [hz, hx, ← sub_eq_add_neg, ← Matrix.sub_mul, ← colJoin_sub, sub_zero]
  obtain ⟨e, he⟩ := trace_inner_rat V p b
  have e₄ : ψ (halfTr (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)))) = 1 := by
    rw [he]
    exact psi_halfTr_incA ψ hψ e
  have e1 : Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v)) =
      -Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)) + Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) y₂) := by
    rw [hz, hy, trace_inner_mul V _ _ _ _ hA, trace_inner_join, inner_neg_right, inner_mul_right, Matrix.trace_neg]
  have e2 : Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b)) := by
    rw [hx, hy, ← Matrix.neg_mul, trace_inner_mul V _ _ _ _ hA]
    have : -colJoin y₁ (0 : Mx D V.rank s) = colJoin (-y₁) (0 : Mx D V.rank s) := by
      rw [← colJoin_neg, neg_zero]
    rw [this, trace_inner_join, inner_zero_left, inner_neg_left, inner_neg_right, inner_mul_right]
    simp
  have e3 : Matrix.trace (HMul.hMul (rat b) (GlobalTheory.StdUnn.inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b))
        - cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)))
        - Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b))
        + Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) := by
    rw [Matrix.trace_mul_comm, ← trace_swap V (rat p) y₁ (rat b) hB, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [Matrix.sub_mul, Matrix.trace_sub]
    exact sub_group _ _ _ _
  have hc := psi_combine ψ _ _ _ _ _ _ _ e1 e2 e3 e₄
  show ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v))) +
      halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) * Φ (rat (colJoin p q * a) + xPart v) = _
  rw [hc, hzx, mul_assoc]
  rfl

end GlobalTheory.CompanionTheory.EisUnfold.Summand
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterEnvelopingCommutesLieStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_enveloping_commutes_lie : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie | exact GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.Clozel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def scalarCurve (s : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (s : ℂ))

theorem scalarCurve_zero : scalarCurve E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 :=
    Units.ext (funext fun _ => by simp [expU])
  rw [scalarCurve, h, map_one]

theorem hasDerivAt_scalarCurve :
    HasDerivAt (fun s => toL (scalarCurve E a s).val) (oneL E a) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro w
  by_cases h : i = j
  · subst h
    have e : (fun s : ℝ => toL (scalarCurve E a s).val i i w) = fun s : ℝ => Complex.exp (s : ℂ) := by
      funext s
      simp [scalarCurve, toL, expU, Matrix.scalar_apply]
    have d : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
      simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    have o : oneL E a i i w = 1 := by simp [oneL, toL]
    rw [e, o]
    exact d
  · have e : (fun s : ℝ => toL (scalarCurve E a s).val i j w) = fun _ : ℝ => 0 := by
      funext s
      simp [scalarCurve, toL, Matrix.scalar_apply, h]
    have o : oneL E a i j w = 0 := by simp [oneL, toL, h]
    rw [e, o]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem eigen_along_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ),
    lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a),
      φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ a φ c hφ t g
  set f : ℝ → ℂ := fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) with hf
  have hd : ∀ u, HasDerivAt f (c * f u) u := by
    intro u
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (scalarCurve E a) (oneL E a)
      scalarCurve_zero hasDerivAt_scalarCurve
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * f u := by
      have := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
      simpa [hf] using this
    rw [h2] at h1
    have h3 : HasDerivAt (fun x : ℝ => φ.1 ((g * GlobalTheory.UnitaryBC.splitCentre E a u) * infGL E a (scalarCurve E a (x - u))))
        (c * f u) u := by
      have h0 : u - u = (0 : ℝ) := sub_self u
      exact HasDerivAt.comp_sub_const u u (by rw [h0]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e : GlobalTheory.UnitaryBC.splitCentre E a x =
        GlobalTheory.UnitaryBC.splitCentre E a u * infGL E a (scalarCurve E a (x - u)) := by
      have := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
      rw [add_sub_cancel] at this
      exact this
    simp only [hf, e, mul_assoc]
  have hP : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v)
      (Complex.exp (-c * u) * (-c) * f u + Complex.exp (-c * u) * (c * f u)) u := by
    intro u
    have h0 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact h0.cexp.mul (hd u)
  have hconst : ∀ u : ℝ, Complex.exp (-c * u) * f u = Complex.exp (-c * (0 : ℝ)) * f 0 := by
    refine fun u => is_const_of_deriv_eq_zero (f := fun v : ℝ => Complex.exp (-c * v) * f v)
      (fun x => (hP x).differentiableAt) (fun x => ?_) u 0
    rw [(hP x).deriv]
    ring
  have h0 : f 0 = φ.1 g := by
    simp [hf, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  have ht := hconst t
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0] at ht
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]
  change f t = _
  rw [← ht, ← mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.CompanionTheory.Clozel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAlongOneParameterPathStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_along_one_parameter_path : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F, (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs | exact GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs | (intros; apply GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationInducedStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_induced : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ),
  ∃ y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), (y : smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).1.1 = eC ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC | exact GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC <;> assumption)
end

