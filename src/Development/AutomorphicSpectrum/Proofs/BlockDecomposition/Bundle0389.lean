import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import GroundTheory.LocalFields.LocalFourierChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import GroundTheory.AutomorphicForms.SmoothRep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (N : ℤ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ valBall k N}
  mul_mem' := by
    intro a b ha hb i
    simpa using add_mem (ha i) (hb i)
  one_mem' := by
    intro i
    simp
  inv_mem' := by
    intro a ha i
    simpa using neg_mem (ha i)

theorem mem_box {n : ℕ} {N : ℤ} {x : Multiplicative (Fin n → k)} :
    x ∈ box k n N ↔ ∀ i, x.toAdd i ∈ valBall k N := Iff.rfl

theorem box_antitone (n : ℕ) {M N : ℤ} (h : M ≤ N) : box k n N ≤ box k n M :=
  fun _ hx i => valBall_antitone h (hx i)

def chi (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) : Multiplicative (Fin n → k) →* ℂˣ where
  toFun x := Circle.toUnits (ψ (a ⬝ᵥ x.toAdd))
  map_one' := by simp
  map_mul' x y := by simp [dotProduct_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : Multiplicative (Fin n → k)) :
    chi k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ x.toAdd)) := rfl

abbrev chiOn (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (H : Subgroup (Multiplicative (Fin n → k))) :
    H →* ℂˣ := (chi k ψ a).comp H.subtype

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun x => MirU_le_Mir k n ⟨x, rfl⟩)

@[simp] theorem coe_unipMir (n : ℕ) (x : Multiplicative (Fin n → k)) :
    ((unipMir k n x : Mir k n) : GL (Fin (n + 1)) k) = unip k n x := rfl

variable {k}

theorem exists_unipMir {n : ℕ} (u : MirUin k n) : ∃ x, unipMir k n x = (u : Mir k n) := by
  obtain ⟨x, hx⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨x, Subtype.ext hx⟩

theorem mem_chi_zero {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) {w : V} (hw : w ∈ twKer τ (MirUin k (m + 1)) 1) :
    w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ 0 ⊤) := by
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨u, w, rfl⟩
  obtain ⟨x, hx⟩ := exists_unipMir u
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w, ?_⟩
  simp [chi_apply, hx]

theorem mem_chi_row {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) (g : GL (Fin (m + 1)) k) {w : V}
    (hw : w ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) :
    τ (levi k (m + 1) g⁻¹) w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤
      (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤) := by
  have hle : twKer τ (MirUin k (m + 1)) (mirChar k ψ m) ≤
      (twKer (τ.comp (unipMir k (m + 1))) ⊤
        (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤)).comap
        (τ (levi k (m + 1) g⁻¹)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    obtain ⟨x, hx⟩ := exists_unipMir u
    set y : Multiplicative (Fin (m + 1) → k) :=
      Multiplicative.ofAdd (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x.toAdd)
      with hy
    have hconj : levi k (m + 1) g⁻¹ * (u : Mir k (m + 1)) = unipMir k (m + 1) y * levi k (m + 1) g⁻¹ := by
      apply Subtype.ext
      show glEmb k (m + 1) g⁻¹ * ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k) = unip k (m + 1) y * glEmb k (m + 1) g⁻¹
      rw [← hx, coe_unipMir, glEmb_mul_unip']
    have hchar : mirChar k ψ m u = chi k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) y := by
      rw [mirChar_eq k ψ m u x (by rw [← hx]; rfl), chi_apply]
      congr 2
      have : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⬝ᵥ y.toAdd =
          ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec y.toAdd) (Fin.last m) := rfl
      rw [this, hy, toAdd_ofAdd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, hconj, map_mul,
      Module.End.mul_apply, hchar]
    exact Submodule.subset_span ⟨⟨y, trivial⟩, τ (levi k (m + 1) g⁻¹) w, rfl⟩
  exact hle hw

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaW

def revMat (A : Type) [CommRing A] (N : ℕ) : Matrix (Fin N) (Fin N) A :=
  (1 : Matrix (Fin N) (Fin N) A).submatrix Fin.rev id

theorem revMat_mul {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    revMat A N * M = M.submatrix Fin.rev id := by
  ext i j
  simp [revMat, Matrix.mul_apply, Matrix.one_apply]

theorem mul_revMat {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    M * revMat A N = M.submatrix id Fin.rev := by
  ext i j
  simp only [revMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro b _ hb
    rw [if_neg, mul_zero]
    intro h
    exact hb (by rw [← h, Fin.rev_rev])
  · simp

theorem revMat_mul_self (A : Type) [CommRing A] (N : ℕ) : revMat A N * revMat A N = 1 := by
  rw [revMat_mul]
  ext i j
  simp [revMat, Matrix.one_apply]

def w₀ (A : Type) [CommRing A] (N : ℕ) : GL (Fin N) A :=
  ⟨revMat A N, revMat A N, revMat_mul_self A N, revMat_mul_self A N⟩

theorem thetaW_eq_conj (A : Type) [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N g = w₀ A N * invT g * (w₀ A N)⁻¹ := by
  apply Units.ext
  show _ = revMat A N * (invT g).1 * revMat A N
  rw [revMat_mul, mul_revMat]
  ext i j
  simp [thetaW, Matrix.reindexAlgEquiv_apply]

def compInvTEquiv {A : Type} [CommRing A] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) A) V) :
    Representation.Equiv (π.comp invT) (π.comp (thetaW A N)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (π (w₀ A N)) (π (w₀ A N)⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun g => LinearMap.ext fun v => by
      show π (w₀ A N) (π (invT g) v) = π (thetaW A N g) (π (w₀ A N) v)
      rw [thetaW_eq_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]

theorem comp_thetaW_equiv_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  intro k _ _ _ _ hGK N V _ _ π hs hi
  obtain ⟨e⟩ := hGK N π hs hi
  exact ⟨(compInvTEquiv π).symm.trans e⟩

end GlobalTheory.CompanionTheory.ThetaW

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocalStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | exact GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | (intros; apply GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFinite
section
namespace GlobalTheory.CompanionTheory.HeckeEnd

open PositivityTheory.Rg.BcB.F.Tail.PExp

theorem hkE_fin : HkEFin := by
  intro G V _ _ _ ρ K f hf v
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset),
    finsum_eq_sum_of_support_subset (s := hf.toFinset), LinearMap.sum_apply]
  · rfl
  all_goals
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    rw [Function.mem_support] at hq
    exact hq (by simp [h])

end GlobalTheory.CompanionTheory.HeckeEnd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorExists
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeKm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_span_unif_pow_iff (m : ℕ) (a : 𝒪[k]) :
    a ∈ Ideal.span {Zls.unif k ^ m} ↔ (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (a : k) ∈ 𝒪[k] := by
  have hc : (((Zls.unifU k ^ m : kˣ)) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k) := by
    simp [Zls.unifU]
    rfl
  have hne : ((Zls.unif k ^ m : 𝒪[k]) : k) ≠ 0 := by
    rw [← hc]; exact Units.ne_zero _
  have hinv : (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hc]
  rw [Ideal.mem_span_singleton', hinv]
  constructor
  · rintro ⟨b, rfl⟩
    have : ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * ((b * Zls.unif k ^ m : 𝒪[k]) : k) = (b : k) := by
      rw [MulMemClass.coe_mul]
      field_simp
    rw [this]
    exact b.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul]
    change ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * (a : k) * _ = _
    field_simp

theorem mem_Km_iff {N m : ℕ} (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j ∈ 𝒪[k] := by
  have key : ∀ (u : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val - 1) i j =
        ((u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j : 𝒪[k]) : k) := by
    intro u i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.map_apply]
      rfl
    · simp [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply_ne h]
      rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq]
    have h := congrArg (fun x : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => x.val i j)
      (MonoidHom.mem_ker.1 hu)
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 (Units.ext (Matrix.ext fun i j => ?_)), rfl⟩
    have h' := h i j
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq] at h'
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h'

theorem continuous_entry_Km (N : ℕ) (c : k) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k => c * (g.val - 1) i j :=
  continuous_const.mul
    (((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).sub continuous_const).matrix_elem i j)

theorem coe_Km_eq (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) = (KO k (Fin N) : Set (GL (Fin N) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin N) k => (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j) ⁻¹'
        (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (show IsOpen (𝒪[k] : Set k) from Valuation.isOpen_integer).preimage (continuous_entry_Km N _ i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
    (show IsCompact (𝒪[k] : Set k) from IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed.preimage
      (continuous_entry_Km N _ i j))

theorem totallyDisconnected_GL (N : ℕ) : TotallyDisconnectedSpace (GL (Fin N) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  exact ⟨(GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_isHeckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ (m : ℕ) (g : GL (Fin N) k), ∃ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m g T := by
  intro k _ _ _ _ N V _ _ π hπ m g
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI := totallyDisconnected_GL (k := k) N
  have hKc := isCompact_Km (k := k) N m
  have hKo := isOpen_Km (k := k) N m
  have hπ' : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hfix : ∀ w : GroundTheory.Automorphic.fixedVectors π (Zls.Km k N m),
      (w : V) ∈ fixed π (Zls.Km k N m) := fun w h => by
    simpa using w.2 h h.2
  refine ⟨LinearMap.codRestrict (fixed π (Zls.Km k N m))
    ((Submodule.subtype _) ∘ₗ GroundTheory.Automorphic.fixedProj π hπ' hKc hKo ∘ₗ π g ∘ₗ
      (fixed π (Zls.Km k N m)).subtype) fun v => hfix _, ?_⟩
  intro v l hl
  have hs := GroundTheory.Automorphic.sub_fixedProj_mem hπ' hKc hKo (π g (v : V))
  have h0 := GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant (ρ := π) (K := Zls.Km k N m) (f := l)
    (fun x hx w => LinearMap.congr_fun (hl x hx) w) hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.HeckeKm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
section
noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.HbBasis

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.LfSt

variable {n : ℕ}

theorem sum_single_one : ∑ a : Fin n, (Matrix.single a a (1 : ℂ) : Mat n) = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun x _ => if_neg fun hx => h (hx.1.symm.trans hx.2)

theorem sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
  GlobalTheory.CompanionTheory.TopClass.sqrt_two_inv_sq

theorem hb_mul_self (a b : Fin n) :
    (hb (a, b) : Mat n) * hb (a, b) = (1 / 2 : ℂ) • (Matrix.single a a 1 + Matrix.single b b 1) := by
  have hs := sqrt_two_inv_sq
  by_cases h : a = b
  · subst h
    have : (hb (a, a) : Mat n) = Matrix.single a a 1 := by simp [hb]
    rw [this, Matrix.single_mul_single_same, ← two_smul ℂ, smul_smul]
    norm_num
  · have hne : b ≠ a := fun e => h e.symm
    by_cases h' : a < b
    · have : (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1) := by
        simp [hb, h, h']
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp [add_comm]
    · have : (hb (a, b) : Mat n) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) • (Matrix.single a b 1 - Matrix.single b a 1) := by
        simp [hb, h, h']
      have hc : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) = -(1 / 2) := by
        calc _ = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (Complex.I * Complex.I) := by ring
          _ = _ := by rw [hs, Complex.I_mul_I]; ring
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp only [mul_one, sub_zero, zero_sub, neg_smul, smul_neg, smul_sub, smul_add]
      abel

theorem sum_hb_mul_self : ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 := by
  rw [Fintype.sum_prod_type]
  simp only [hb_mul_self, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, sum_single_one]
  rw [← Nat.cast_smul_eq_nsmul ℂ n (1 : Mat n), ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem coords_one (p : Fin n × Fin n) : ((coords (1 : Mat n) p : ℝ) : ℂ) = (hb p : Mat n).trace := by
  have := GlobalTheory.CompanionTheory.ConeLin.re_trace (1 : Mat n) (by simp) p
  simpa [coords] using this

theorem hOf_coords {H : Mat n} (hH : H.IsHermitian) : hOf (coords H) = H :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_re H hH

theorem coords_hOf (v : Fin n × Fin n → ℝ) : coords (hOf v) = v := by
  funext q
  have : (hOf v * hb q).trace = (v q : ℂ) := by
    classical
    simp [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]
  simp [coords, this]

theorem hOf_isHermitian (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_herm v

theorem sum_trace_smul_hb : ∑ p, (hb p : Mat n).trace • hb p = 1 := by
  have h := hOf_coords (H := (1 : Mat n)) Matrix.isHermitian_one
  simpa only [hOf, coords_one] using h

theorem oPt_mem_cone : oPt n ∈ cone n := by
  show (hOf (coords (1 : Mat n))).PosDef
  rw [hOf_coords Matrix.isHermitian_one]
  exact Matrix.PosDef.one

theorem hbFacts : HbFacts := fun _ =>
  ⟨GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb, fun _ hH => hOf_coords hH,
    coords_hOf, hOf_isHermitian, sum_hb_mul_self, sum_trace_smul_hb, oPt_mem_cone⟩

end GlobalTheory.CompanionTheory.HbBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleOfDiscreteSeriesDatumStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepIrred := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | exact GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityNeZeroSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JmSub

theorem exists_subQuot_of_jm_ne_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 →
      ∃ S T : Subrepresentation (jac (stdBlocks (fun a => (x a).1) hd) π),
        Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  intro k _ _ _ _ h N x hd V _ _ π hjm
  obtain ⟨r, hr, hpos⟩ : ∃ r, GlobalTheory.SmGL.OccursTimes (GlobalTheory.SmGL.piTensor fun a => (x a).rep)
      (GlobalTheory.SmGL.jac (GlobalTheory.SmGL.stdBlocks (fun a => (x a).1) hd) π) r ∧ 0 < r := by
    by_contra hcon
    apply hjm
    unfold Zc.jm GlobalTheory.SmGL.jhMult
    refine le_antisymm (iSup_le fun r => iSup_le fun hr' => ?_) zero_le
    have hr0 : r = 0 := by
      by_contra hne
      exact hcon ⟨r, hr', Nat.pos_of_ne_zero hne⟩
    simp [hr0]
  obtain ⟨S, T, -, -, hST⟩ := hr
  exact ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hST ⟨0, hpos⟩⟩

end GlobalTheory.CompanionTheory.JmSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_subquotient_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL k) (hy : ∑ a, (y a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P), jm y hy π ≤ jm y hy P := by
  first | exact @GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | exact GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquiv
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LUniq

theorem isL_unique : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    LOrderFree k → ∀ (𝔭 : Multiset (Segment k)) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W),
    IsL 𝔭 π → IsL 𝔭 σ → Nonempty (π.Equiv σ) := by
  intro k _ _ _ _ hLO 𝔭 N V W _ _ _ _ π σ hπ hσ
  obtain ⟨h, x, hd, hx, hπc⟩ := hπ
  have hσc : IsCosocle σ (prodIrr x hd) := hLO 𝔭 h N x hd hx σ hσ
  exact hσc.unique hπc

end GlobalTheory.CompanionTheory.LUniq
end

