import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0730
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
import BuildAid.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesMeasurePreserving
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem map_comp_comap {H Y Z : Type} [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
    (e : H ≃ᵐ Y) (ν : Measure Y) {c : Y → Z} (hc : Measurable c) :
    (Measure.comap e ν).map (c ∘ e) = ν.map c := by
  rw [← MeasurableEquiv.map_symm, ← Measure.map_map hc e.measurable,
    Measure.map_map e.measurable e.symm.measurable]
  have : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
  rw [this, Measure.map_id]

theorem map_prod_box {R K P : Type} [MeasurableSpace R] [MeasurableSpace K] [Fintype P] {n d : ℕ}
    (lam : Measure R) [SigmaFinite lam] (κ : Measure K) [SigmaFinite κ] (r : K → Fin d → R)
    (hr : Measurable r) (hκ : κ.map r = Measure.pi fun _ => lam) :
    ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : P => κ)).map
        (fun x : (Fin n → R) × (P → K) =>
          (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) =
      Measure.pi fun _ : Fin n ⊕ (Fin d × P) => lam := by
  have hc : Measurable (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hc (MeasurableSet.univ_pi hs)]
  have hset : (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) ⁻¹'
        Set.pi Set.univ s =
      (Set.pi Set.univ fun i : Fin n => s (Sum.inl i)) ×ˢ
        (Set.pi Set.univ fun p : P => r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
      Sum.forall, Sum.elim_inl, Sum.elim_inr, Prod.forall]
    exact and_congr Iff.rfl ⟨fun h p k => h k p, fun h k p => h p k⟩
  have hκs : ∀ p : P, κ (r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) =
      ∏ k : Fin d, lam (s (Sum.inr (k, p))) := fun p => by
    rw [← Measure.map_apply hr (MeasurableSet.univ_pi fun k => hs _), hκ, Measure.pi_pi]
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type,
    Fintype.prod_prod_type]
  simp only [hκs]
  rw [Finset.prod_comm]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem coordHerm_map_hCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map (hCo R σ b) = Measure.pi fun _ : Idx n d => lam := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam hlam
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK R b lam) := inferInstance

  let r : R ⊗[F] E → Fin d → R := fun y k => (Algebra.TensorProduct.basis R b).repr y k
  let Tr : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph r
  have hr : Measurable r := Tr.toMeasurableEquiv.measurable
  have hκ : (GlobalTheory.CompanionTheory.SW.coordK R b lam).map r = Measure.pi fun _ => lam := by
    have := map_comp_comap Tr.toMeasurableEquiv (Measure.pi fun _ => lam) (c := id) measurable_id
    rw [Measure.map_id] at this
    exact this

  let T := (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6).homeomorph
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n)
  have hbox := map_prod_box (n := n) (P := {p : Fin n × Fin n // p.1 < p.2}) lam
    (GlobalTheory.CompanionTheory.SW.coordK R b lam) r hr hκ
  have hc : Measurable (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  have hm := map_comp_comap T.toMeasurableEquiv
    ((Measure.pi fun _ : Fin n => lam).prod
      (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => GlobalTheory.CompanionTheory.SW.coordK R b lam)) hc
  rw [hbox] at hm
  have hfun : hCo R σ b = (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) ∘
      T.toMeasurableEquiv := by
    funext S i
    rcases i with i | q <;> rfl
  rw [hfun]
  exact hm

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesNaturalInRing
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem repr_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem trace_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      f (Algebra.trace R (R ⊗[F] E) x) := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Algebra.TensorProduct.map f (AlgHom.id F E) (x * Algebra.TensorProduct.basis R b k) =
      Algebra.TensorProduct.map f (AlgHom.id F E) x * Algebra.TensorProduct.basis R' b k := by
    rw [_root_.map_mul]
    simp [Algebra.TensorProduct.basis_apply]
  rw [← repr_map_tensor f b, h]

theorem hCo_hermMap : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d), hCo R' σ b (hermMap f σ S) i = f (hCo R σ b S i) := by
  intro F E _ _ _ σ R R' _ _ _ _ f d b n S i
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, hermMap, Matrix.map_apply, map_mul, AlgHom.commutes, trace_map_tensor f b]
  · simp only [hCo, Sum.elim_inr, hermMap, Matrix.map_apply, repr_map_tensor f b]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_mul_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x y : E) :
    Algebra.trace F E (σ x * y) = Algebra.trace F E (x * σ y) := by
  have hinv : Function.Involutive σ := GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol h
  have key := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ hinv.bijective) (σ x * y)
  rw [← key]
  simp [hinv x]

theorem trace_sigR_mul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u w : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * w) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr u k *
        ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * (Algebra.TensorProduct.basis R b).repr w l := by
  set C := Algebra.TensorProduct.basis R b with hC
  have hC' : ∀ (r : R) (k : Fin d), r • C k = r ⊗ₜ[F] b k := by
    intro r k
    simp [hC, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  conv_lhs => rw [← C.sum_repr u, ← C.sum_repr w]
  simp only [hC', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : sigR R σ (C.repr u k ⊗ₜ[F] b k) = C.repr u k ⊗ₜ[F] σ (b k) := by simp [sigR]
  rw [hs, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.GaussMean.OneVec.trace_tmul, trace_mul_sig h]
  ring

theorem mulVec_inl (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (i : Fin n) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inl i) = v (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, coordForm, Matrix.one_apply]

theorem mulVec_inr (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (k : Fin d)
    (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inr (k, q)) =
      ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * v (Sum.inr (l, q)) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, coordForm, Matrix.map_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.blockDiagonal_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single q]
  · simp
  · intro x _ hx
    simp [hx, Ne.symm hx]
  · simp

theorem pairHerm_eq_coordForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n),
    pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  intro F E _ _ _ _ _ σ h R _ _ d b n S T
  rw [GlobalTheory.HermCoordEquiv.pair_eq R h S T]
  unfold GlobalTheory.HermSD.coordPair
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [mulVec_inl, Fintype.sum_prod_type, mulVec_inr]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_sigR_mul h]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrabilityStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_section_local_integrability : IkLint := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.ikLint | exact GlobalTheory.CompanionTheory.ColumnSplitting.ikLint | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.ikLint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingIteratedDerivative
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult
  GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.BZShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpowM_half_cancel {n : ℕ} (m : ℕ) (p : Mir k n) :
    ((dpowM n (-(m : ℝ) / 2) p : ℂˣ) : ℂ) * ((dpowM n (-(m : ℝ) / 2) p : ℂˣ) : ℂ) *
      ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = 1 := by
  have h : dpowM (k := k) n (-(m : ℝ) / 2) * dpowM n (-(m : ℝ) / 2) * dpowM n (m : ℝ) = 1 := by
    rw [← DerivTw.dpowM_add, ← DerivTw.dpowM_add,
      show (m : ℝ) + (-(m : ℝ) / 2 + -(m : ℝ) / 2) = 0 by ring, DerivTw.dpowM_zero]
  have h2 := congrArg (fun f : Mir k n →* ℂˣ => ((f p : ℂˣ) : ℂ)) h
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one] at h2
  have h3 : ((dpowM n (m : ℝ) p : ℂˣ) : ℂ) =
      ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) := by
    show ((detChar (Fin (n + 1)) (absPow k (((m : ℝ)) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = _
    rw [Complex.ofReal_natCast]
  rw [← h3]
  exact h2

theorem pair_iterN (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (π π' : GRep k (((m + 1) + m) + 1))
    (hs : IsSmooth π.ρ) (hs' : IsSmooth π'.ρ) (B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π.ρ g v) (π'.ρ g v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) :
    ∃ B' : (iterN ψ m (gres π)).V →ₗ[ℂ] (iterN ψ⁻¹ m (gres π')).V →ₗ[ℂ] ℂ,
      (∀ p v v', B' ((iterN ψ m (gres π)).ρ p v) ((iterN ψ⁻¹ m (gres π')).ρ p v') = B' v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B' v v' ≠ 0 := by
  obtain ⟨B₀, hB₀, hn₀⟩ := GlobalTheory.CompanionTheory.BZPairDescend.pair_iterPhi ψ hc h1 m m π.ρ π'.ρ hs hs' B hB hn
  obtain ⟨e⟩ : MIso (iterN ψ m (gres π)) (mtw (iterPhi k ψ m (resM k π.ρ)) (-(m : ℝ) / 2)) := DerivTw.iterN_iso ψ m (gres π)
  obtain ⟨e'⟩ : MIso (iterN ψ⁻¹ m (gres π')) (mtw (iterPhi k ψ⁻¹ m (resM k π'.ρ)) (-(m : ℝ) / 2)) :=
    DerivTw.iterN_iso ψ⁻¹ m (gres π')
  let f : (iterN ψ m (gres π)).V ≃ₗ[ℂ] (iterPhi k ψ m (resM k π.ρ)).V := e.toLinearEquiv
  let f' : (iterN ψ⁻¹ m (gres π')).V ≃ₗ[ℂ] (iterPhi k ψ⁻¹ m (resM k π'.ρ)).V := e'.toLinearEquiv
  have hf : ∀ p v, f ((iterN ψ m (gres π)).ρ p v) =
      ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ m (resM k π.ρ)).ρ p (f v) := fun p v => eint e p v
  have hf' : ∀ p v, f' ((iterN ψ⁻¹ m (gres π')).ρ p v) =
      ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ⁻¹ m (resM k π'.ρ)).ρ p (f' v) := fun p v => eint e' p v
  refine ⟨(B₀.compl₁₂ f.toLinearMap f'.toLinearMap), fun p v v' => ?_, fun v hv => ?_⟩
  · simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hf, hf', map_smul, map_smul, LinearMap.smul_apply, hB₀, smul_eq_mul, smul_eq_mul]
    linear_combination (B₀ (f v) (f' v')) * dpowM_half_cancel (k := k) m p
  · obtain ⟨w', hw'⟩ := hn₀ (f v) (by simpa using hv)
    refine ⟨f'.symm w', ?_⟩
    simpa using hw'

end GlobalTheory.CompanionTheory.BZShell

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingSegmentProduct
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.BZShell

namespace GlobalTheory.CompanionTheory.BZShell.SwapPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem contra_ind₂_swap {r t N : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (hs₁ : IsSmooth π₁) (hi₁ : π₁.IsIrreducible) (hs₂ : IsSmooth π₂) (hi₂ : π₂.IsIrreducible)
    (h : r + t = N) (h' : t + r = N) (hX : (ind₂ (stdSum h) (extTensor π₁ π₂)).IsIrreducible) :
    Nonempty ((contra (ind₂ (stdSum h) (extTensor π₁ π₂))).Equiv
      (ind₂ (stdSum h') (extTensor (contra π₂) (contra π₁)))) := by
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have Gx := nonempty_comp_invT_equiv_contra π₁ (hA k _ _ _ hs₁ hi₁) hi₁
  have Gy := nonempty_comp_invT_equiv_contra π₂ (hA k _ _ _ hs₂ hi₂) hi₂
  have T := nonempty_extTensor_swap π₁ π₂
  have K := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h') (extTensor π₁ π₂)
  have GX := nonempty_comp_invT_equiv_contra (ind₂ (stdSum h) (extTensor π₁ π₂))
    (hA k N _ _ (isSmooth_parInd _ _) hX) hX
  exact Gx.elim fun gx => Gy.elim fun gy => T.elim fun τ => K.elim fun κ => GX.elim fun gX =>
    ⟨gX.symm.trans (κ.symm.trans (ind₂Equiv _ (τ.trans (extTensorCongr gy gx))))⟩

theorem ind₂_contra_fam (F : Fin 2 → IrrGL k) {N : ℕ} (h : (F 0).1 + (F 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra (F 0).rep) (contra (F 1).rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep)))) := by
  have hd : ∑ a, (F a).1 = N := (Fin.sum_univ_two _).trans h
  have E₂ := nonempty_ind₂_contra_equiv GlobalTheory.CompanionTheory.BZCuspPair.irrAdm F hd h
  have E₁ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h fun a => (F a).rep
  refine E₂.elim fun ε₂ => E₁.elim fun ε₁ => ?_
  have ε₃ : (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep)).Equiv (prodIrr F hd) := ε₁
  have ε₄ : (contra (prodIrr F hd)).Equiv (contra (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep))) :=
    GlobalTheory.ContraRefl.contraEquiv ε₃
  exact ⟨ε₂.trans ε₄⟩

theorem induced_two_contragredient_equiv (F : Fin 2 → IrrGL k) (x y : IrrGL k) (h₀ : F 0 = x) (h₁ : F 1 = y) {N : ℕ}
    (h : x.1 + y.1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra x.rep) (contra y.rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor x.rep y.rep)))) := by
  subst h₀ h₁
  exact ind₂_contra_fam F h

theorem ind₂_contra_rep (x y : IrrGL k) {N : ℕ} (h : x.1 + y.1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra x.rep) (contra y.rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor x.rep y.rep)))) :=
  induced_two_contragredient_equiv ![x, y] x y rfl rfl h

theorem ind₂_contra_of_equiv (x y : IrrGL k) {N : ℕ} (h : x.1 + y.1 = N)
    (π₁ : Representation ℂ (GL (Fin x.1) k) V) (π₂ : Representation ℂ (GL (Fin y.1) k) W)
    (φ₁ : π₁.Equiv x.rep) (φ₂ : π₂.Equiv y.rep) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra π₁) (contra π₂))).Equiv
      (contra (ind₂ (stdSum h) (extTensor π₁ π₂)))) :=
  (ind₂_contra_rep x y h).elim fun ε =>
    ⟨(ind₂Equiv _ (extTensorCongr (GlobalTheory.ContraRefl.contraEquiv φ₁.symm) (GlobalTheory.ContraRefl.contraEquiv φ₂.symm))).trans
      (ε.trans (GlobalTheory.ContraRefl.contraEquiv (ind₂Equiv _ (extTensorCongr φ₁ φ₂))))⟩

theorem ind₂_contra_equiv {r t N : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W)
    (hs₁ : IsSmooth π₁) (hi₁ : π₁.IsIrreducible) (hs₂ : IsSmooth π₂) (hi₂ : π₂.IsIrreducible) (h : r + t = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra π₁) (contra π₂))).Equiv
      (contra (ind₂ (stdSum h) (extTensor π₁ π₂)))) :=
  ind₂_contra_of_equiv (IrrGL.of π₁ hs₁ hi₁) (IrrGL.of π₂ hs₂ hi₂) h π₁ π₂
    (IrrGL.equivOf π₁ hs₁ hi₁) (IrrGL.equivOf π₂ hs₂ hi₂)

theorem exists_form_of_equiv_contra {N : ℕ} (A : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth A)
    (C : Representation ℂ (GL (Fin N) k) W) (E : C.Equiv (contra A)) :
    ∃ B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, (∀ g v v', B (A g v) (C g v') = B v v') ∧ ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  let B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ := LinearMap.flip ((smoothPart A.dual).subtype ∘ₗ E.toLinearEquiv.toLinearMap)
  have hB : ∀ v v', B v v' = ((E.toLinearEquiv v' : smoothPart A.dual) : Module.Dual ℂ V) v := fun _ _ => rfl
  refine ⟨B, fun g v v' => ?_, fun v hv => ?_⟩
  · have hE : E.toLinearEquiv (C g v') = contra A g (E.toLinearEquiv v') :=
      E.toIntertwiningMap.isIntertwining _ _ g v'
    rw [hB, hB, hE, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k N) hv
    refine ⟨E.toLinearEquiv.symm l, ?_⟩
    rw [hB, LinearEquiv.apply_symm_apply]
    exact hl

theorem isIrreducible_ind₂_segTerm {a N : ℕ} (π : Representation ℂ (GL (Fin a) k) V) (hN : 2 * a = N) (h : a + a = N)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 a) (segTerm π 2)).IsIrreducible) :
    (ind₂ (stdSum h) (extTensor (segTerm π 2 0) (segTerm π 2 1))).IsIrreducible := by
  subst hN
  have hd : ∑ _ : Fin 2, a = 2 * a := by simp
  obtain ⟨E⟩ := nonempty_ind₂_equiv_multiProd (d := fun _ : Fin 2 => a) hd h (X := fun _ => V) (segTerm π 2)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin 2) (Fin (2 * a)) (fun _ => Fin a)
    (stdBlocks (fun _ : Fin 2 => a) hd) (GlobalTheory.Published.consecBlocks 2 a) _).1 (piTensor (segTerm π 2))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E.trans ψ).symm hirr

theorem segTerm_zero {a : ℕ} (π : Representation ℂ (GL (Fin a) k) V) : segTerm π 2 0 = π := by
  have h : detChar (Fin a) (absPow k (((0 : Fin 2) : ℕ) : ℂ)) = 1 := by
    ext g
    simp
  rw [segTerm, h, twist_one]

theorem segTerm_one {a : ℕ} (π : Representation ℂ (GL (Fin a) k) V) : segTerm π 2 1 = twist π (dpow a 1) := by
  simp [segTerm, dpow]

theorem product_two_contragredient_equiv {a : ℕ} (σ : IrrRep (GL (Fin a) k))
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 a) (segTerm σ.ρ 2)).IsIrreducible) :
    Nonempty ((prod2 (k := k) rfl (contra σ.ρ) (twist (contra σ.ρ) (dpow a (-1)))).Equiv
      (contra (prod2 (k := k) rfl (twist σ.ρ (dpow a 1)) σ.ρ))) := by
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hs := σ.smooth
  have hi := σ.irr
  have hs₁ : IsSmooth (twist σ.ρ (dpow (k := k) a 1)) := isSmooth_twist hs (isSmoothChar_absPow _).detChar
  have hi₁ : (twist σ.ρ (dpow (k := k) a 1)).IsIrreducible := isIrreducible_twist hi _
  have hX : (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor σ.ρ (twist σ.ρ (dpow (k := k) a 1)))).IsIrreducible := by
    have h := isIrreducible_ind₂_segTerm σ.ρ (by omega : 2 * a = a + a) rfl hirr
    rwa [segTerm_zero, segTerm_one] at h
  have S := contra_ind₂_swap σ.ρ (twist σ.ρ (dpow (k := k) a 1)) hs hi hs₁ hi₁ rfl rfl hX
  have B₁ := ind₂_contra_equiv σ.ρ (twist σ.ρ (dpow (k := k) a 1)) hs hi hs₁ hi₁ rfl
  have B₂ := ind₂_contra_equiv (twist σ.ρ (dpow (k := k) a 1)) σ.ρ hs₁ hi₁ hs hi rfl
  have Tw : Nonempty ((twist (contra σ.ρ) (dpow (k := k) a (-1))).Equiv (contra (twist σ.ρ (dpow (k := k) a 1)))) :=
    GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist hA σ.ρ hs hi (isSmoothChar_absPow _) (isSmoothChar_absPow _)
      (by rw [Complex.ofReal_neg, absPow_neg, mul_inv_cancel])
  have P₁ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv (k := k) (contra σ.ρ) (twist (contra σ.ρ) (dpow (k := k) a (-1)))
  have P₂ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv (k := k) (twist σ.ρ (dpow (k := k) a 1)) σ.ρ
  refine S.elim fun s => B₁.elim fun b₁ => B₂.elim fun b₂ => Tw.elim fun τ => P₁.elim fun p₁ => P₂.elim fun p₂ => ?_
  have c₁ : (prod2 (k := k) rfl (contra σ.ρ) (twist (contra σ.ρ) (dpow a (-1)))).Equiv
      (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor (contra σ.ρ) (contra (twist σ.ρ (dpow (k := k) a 1))))) :=
    p₁.trans (ind₂Equiv _ (extTensorCongr (.refl _) τ))
  have c₂ : (contra (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor (twist σ.ρ (dpow (k := k) a 1)) σ.ρ))).Equiv
      (contra (prod2 (k := k) rfl (twist σ.ρ (dpow a 1)) σ.ρ)) :=
    GlobalTheory.ContraRefl.contraEquiv p₂
  exact ⟨c₁.trans (b₁.trans (s.trans (b₂.trans c₂)))⟩

theorem exists_pairing_cast (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k))
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible) {N : ℕ}
    (h : (m + 1) + (m + 1) = N) :
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast h).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast h).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast h |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast h |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  subst h
  exact (product_two_contragredient_equiv σ hirr).elim fun E =>
    exists_form_of_equiv_contra (prod2 (k := k) rfl (twist σ.ρ (dpow (m + 1) 1)) σ.ρ) (isSmooth_parInd _ _) _ E

theorem exists_invariant_pairing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible),
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m)).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m)).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m) |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m) |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 :=
  fun m σ _ hirr => exists_pairing_cast m σ hirr (size_eq m)

end GlobalTheory.CompanionTheory.BZShell.SwapPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectorsStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_finite_irreducible_fixed_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  first | exact @GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | exact GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | (intros; apply GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBoundStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_height_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | exact GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorantStatement
section
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_majorant : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | exact GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | (intros; apply GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts <;> assumption)
end

