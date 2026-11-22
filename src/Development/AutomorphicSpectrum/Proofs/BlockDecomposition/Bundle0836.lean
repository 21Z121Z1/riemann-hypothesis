import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import GroundTheory.GlobalFields.Adele.Discrete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0830
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponents
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0831
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0832
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSet
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi.Den

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (Fv F v) t) = v.valuation F t :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t

theorem exists_valued_bound (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)} (hC : IsCompact C) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ x ∈ C, Valued.v x ≤ γ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover
    (fun x => {y : Fv F v | y - x ∈ v.adicCompletionIntegers F}) (fun x _ => by
      have hopen : IsOpen {y : Fv F v | y - x ∈ v.adicCompletionIntegers F} :=
        hO.preimage (continuous_id.sub continuous_const)
      exact hopen.mem_nhds (by simp))
  obtain ⟨M, hM⟩ := (s.image fun x => Valued.v x).exists_le
  refine ⟨max M 1, (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).ne', fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
  have h1 : Valued.v (y - x) ≤ 1 := hxy
  have h2 : Valued.v x ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have h3 : y = (y - x) + x := by ring
  rw [h3]
  exact (Valuation.map_add _ _ _).trans
    (max_le (h1.trans (le_max_right _ _)) (h2.trans (le_max_left _ _)))

theorem exists_finset_inv_integral {D : Set (AF F)ˣ} (hD : IsCompact D) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ u ∈ D, ∀ v, v ∉ T →
      ((u⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  obtain ⟨s, -, hs⟩ := hD.elim_nhds_subcover
    (fun a : (AF F)ˣ => {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F}) (fun a _ => by
      have hopen : IsOpen {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F} :=
        (IdeleGroup.isOpen_standardOpenSubgroup F).preimage (continuous_const.mul continuous_id)
      exact hopen.mem_nhds (by simp [one_mem]))
  have hfin : ∀ a : (AF F)ˣ, {v : HeightOneSpectrum (𝓞 F) |
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∉ v.adicCompletionIntegers F}.Finite := fun a =>
    Filter.eventually_cofinite.mp ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  refine ⟨s.biUnion fun a => (hfin a).toFinset, fun u hu v hv => ?_⟩
  obtain ⟨a, ha, hau⟩ := Set.mem_iUnion₂.mp (hs hu)
  have hav : ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
    by_contra hcon
    exact hv (Finset.mem_biUnion.mpr ⟨a, ha, (hfin a).mem_toFinset.mpr hcon⟩)
  have hh := ((IdeleGroup.mem_standardOpenSubgroup F).mp hau v).2
  have hu' : u⁻¹ = (a⁻¹ * u)⁻¹ * a⁻¹ := by group
  have hmul : ((u⁻¹ : (AF F)ˣ) : AF F).2 v =
      (((a⁻¹ * u)⁻¹ : (AF F)ˣ) : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := by
    conv_lhs => rw [hu']
    rfl
  rw [hmul]
  exact mul_mem hh hav

theorem exists_inv_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ u ∈ D, Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ γ := by
  have hc : Continuous fun u : (AF F)ˣ => ((u⁻¹ : (AF F)ˣ) : AF F).2 v :=
    Units.continuous_val.comp ((IdeleGroup.continuous_finiteProj (K := F) v).comp continuous_inv)
  obtain ⟨γ, h0, hγ⟩ := exists_valued_bound v (hD.image hc)
  exact ⟨γ, h0, fun u hu => hγ _ (Set.mem_image_of_mem _ hu)⟩

theorem exists_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (A : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)),
      ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
        (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
        ∀ v, v.valuation F t ≤ if v ∈ T then A v else 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_finset_inv_integral hD
  choose B _ hB using fun v => exists_inv_bound hD v
  have hG : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ : WithZero (Multiplicative ℤ), v ∈ S →
      ∀ x ∈ C v, Valued.v x ≤ γ := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨γ, -, h⟩ := exists_valued_bound v (hC v hv)
      exact ⟨γ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose G hG using hG
  refine ⟨T₀ ∪ S, fun v => max (G v) 1 * B v, fun u hu t h1 h2 v => ?_⟩
  have hinv : (u : AF F).2 v * ((u⁻¹ : (AF F)ˣ) : AF F).2 v = 1 :=
    congrArg (fun a : AF F => a.2 v) (Units.mul_inv u)
  have hx : algebraMap F (Fv F v) t =
      (algebraMap F (Fv F v) t * (u : AF F).2 v) * ((u⁻¹ : (AF F)ˣ) : AF F).2 v := by
    rw [mul_assoc, hinv, mul_one]
  have hval : v.valuation F t = Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) *
      Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) := by
    rw [← valued_algebraMap, ← map_mul, ← hx]
  have hfirst : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ max (G v) 1 := by
    by_cases hv : v ∈ S
    · exact (hG v hv _ (h1 v hv)).trans (le_max_left _ _)
    · have a : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hv
      exact a.trans (le_max_right _ _)
  by_cases hvT : v ∈ T₀ ∪ S
  · rw [if_pos hvT, hval]
    exact mul_le_mul' hfirst (hB v u hu)
  · rw [if_neg hvT, hval]
    have hvS : v ∉ S := fun h => hvT (Finset.mem_union_right _ h)
    have hvT₀ : v ∉ T₀ := fun h => hvT (Finset.mem_union_left _ h)
    have a1 : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hvS
    have a2 : Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ 1 := hT₀ u hu v hvT₀
    simpa using mul_le_mul' a1 a2

theorem valuation_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    v.valuation F (n : F) ≤ 1 := by
  have := HeightOneSpectrum.valuation_le_one (K := F) v (n : 𝓞 F)
  simpa using this

theorem exists_nat_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (A : WithZero (Multiplicative ℤ)) :
    ∃ n : ℕ, 0 < n ∧ v.valuation F (n : F) * A ≤ 1 := by
  by_cases hA : A = 0
  · exact ⟨1, one_pos, by simp [hA]⟩
  have hlt : v.valuation F ((Ideal.absNorm v.asIdeal : ℕ) : F) < 1 := by
    have h := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
      (Ideal.absNorm_mem _)
    simpa using h
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (inv_ne_zero hA))
  have hpos : 0 < Ideal.absNorm v.asIdeal := by
    refine Nat.pos_of_ne_zero fun h => v.ne_bot ?_
    exact Ideal.absNorm_eq_zero_iff.mp h
  refine ⟨Ideal.absNorm v.asIdeal ^ k, pow_pos hpos k, ?_⟩
  have h3 : v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) < A⁻¹ := by
    push_cast
    rw [map_pow]
    exact hk
  calc v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) * A ≤ A⁻¹ * A :=
        mul_le_mul' h3.le le_rfl
    _ = 1 := inv_mul_cancel₀ hA

theorem common_denominator (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ) (hD : IsCompact D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  obtain ⟨T, A, hA⟩ := exists_bound hD S C hC
  choose n hn0 hn using fun v => exists_nat_mul_le_one (F := F) v (A v)
  refine ⟨∏ v ∈ T, n v, Finset.prod_pos fun v _ => hn0 v, fun u hu t h1 h2 => ?_⟩
  refine exists_eq_of_forall_mem_adicCompletionIntegers F _ fun v => ?_
  rw [coe_mem_adicCompletionIntegers_iff, map_mul]
  have ht := hA u hu t h1 h2 v
  by_cases hv : v ∈ T
  · rw [if_pos hv] at ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hv
    have hN : v.valuation F (((∏ v ∈ T, n v : ℕ)) : F) ≤ v.valuation F (n v : F) := by
      rw [hm]
      push_cast
      rw [map_mul]
      simpa using mul_le_mul' (le_refl (v.valuation F (n v : F))) (valuation_natCast_le_one v m)
    exact (mul_le_mul' hN ht).trans (hn v)
  · rw [if_neg hv] at ht
    simpa using mul_le_mul' (valuation_natCast_le_one v (∏ v ∈ T, n v)) ht

end GlobalTheory.CompanionTheory.BasePsi.Den

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitianStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_pairing_local_hermitian : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n), (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) → ∀ β : HermE D n, pch ψ x.1 (rat β.1) = psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split | exact GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split | (intros; apply GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisCM

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open PositivityTheory.RgEis

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

def glEquiv (e : R ≃+* R') : GL ι R ≃* GL ι R' := Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem coe_glEquiv (e : R ≃+* R') (g : GL ι R) :
    ((glEquiv e g : GL ι R') : Matrix ι ι R') = (g : Matrix ι ι R).map e := rfl

theorem coe_glEquiv_inv (e : R ≃+* R') (g : GL ι R) :
    (((glEquiv e g)⁻¹ : GL ι R') : Matrix ι ι R') = ((g⁻¹ : GL ι R) : Matrix ι ι R).map e := by
  rw [← map_inv]; rfl

theorem mem_stab_iff (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    g ∈ stab R s ↔ glEquiv e g ∈ stab R' s := by
  change (∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]

variable {E : Type} [Field E]

theorem mem_kGL_iff (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hO : ∀ x, x ∈ A.O ↔ e x ∈ B.O)
    (hφ : ∀ w, ∃ w', ∀ x, A.φ w x = B.φ w' (e x)) (hφ' : ∀ w', ∃ w, ∀ x, A.φ w x = B.φ w' (e x)) (g : GL ι R) :
    g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι := by
  change ((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]
  refine and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩
  · obtain ⟨w, hw⟩ := hφ' w'
    have : ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w) := by
      ext r c; simp [hw]
    rw [this]; exact h w
  · obtain ⟨w', hw⟩ := hφ w
    have : (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w') := by
      ext r c; simp [hw]
    rw [this]; exact h w'

theorem iwa_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι)
    (s : Set ι) (h : Iwa (stab R' s) (B.kGL ι)) : Iwa (stab R s) (A.kGL ι) := by
  intro g
  obtain ⟨p, hp, k, hk', hg⟩ := h (glEquiv e g)
  refine ⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩
  · rw [mem_stab_iff e]; simpa using hp
  · rw [hk]; simpa using hk'
  · apply (glEquiv e).injective
    simp [hg]

variable [TopologicalSpace R] [TopologicalSpace R']

theorem continuous_glEquiv (e : R ≃+* R') (h : Continuous e) : Continuous (glEquiv (ι := ι) e) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id h)

theorem kcpt_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (h1 : Continuous e) (h2 : Continuous e.symm)
    (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι) (h : IsCompact (B.kGL ι : Set (GL ι R'))) :
    IsCompact (A.kGL ι : Set (GL ι R)) := by
  let H : GL ι R ≃ₜ GL ι R' :=
    { toEquiv := (glEquiv e).toEquiv
      continuous_toFun := continuous_glEquiv e h1
      continuous_invFun := continuous_glEquiv e.symm h2 }
  have : (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R')) := by
    ext g; exact hk g
  rw [this]
  exact H.isCompact_preimage.2 h

end Transport

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]
  | add x y hx hy => simp [map_add, hx, hy]

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : Module.Finite (AF F) (AE F E) := inferInstance
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem cA_mem_intHat (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ intHat F E) : cA σ z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, o, rfl⟩ := hz
    have ho : IsIntegral ℤ (σ (o : E)) := (RingOfIntegers.isIntegral_coe o).map σ
    refine AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩
    rw [map_smul, cA_inclR]
    rfl
  | zero => simp [zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end CM

theorem cmGood : StdGood → Dict → DictInf → CMGood := by
  intro hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres
  have hs := hS E
  obtain ⟨d1, d2, d3, d4, -⟩ := hD F E
  have hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O := fun x => Iff.rfl
  have hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)),
      g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι := fun ι _ _ g =>
    mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g
  have hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom) := Continuous.units_map _ d1
  have hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F := F) (AF F)).toMonoidHom x) =
      Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine ⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hs.iinj
    change algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y
    rw [← d3, ← d3]
    exact congrArg _ hxy
  · intro x y
    change (adStd E).lg (Units.map _ (x * y)) = _
    rw [map_mul]
    exact hs.lgmul _ _
  · exact hs.lgcont.comp hu
  · intro x
    exact (congrArg (adStd E).lg (hi x)).trans (hs.lgi x)
  · intro ι _ _
    exact kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)
  · intro ι _ _ s
    exact iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)
  · intro x hx
    have h1 : finOne F • x ∈ intHat F E := (d4 x).1 hx
    refine (d4 _).2 ?_
    have h2 := cA_mem_intHat σ h1
    rwa [map_smul] at h2
  · intro w x
    exact (hI F E σ hcm).1 w x
  · intro x
    exact ⟨σ x, cA_inclR σ x⟩
  · intro x
    exact ResEtaPow.map_conj hξ hres x

end GlobalTheory.CompanionTheory.RgEisCM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponentsStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_formula_of_components : Tate → PsiSide → Ratio → HEx → TestEx → Dens → LSide → ThetaId → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | exact GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | (intros; apply GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummableStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_terms_uniformly_summable : ∀ {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {s : ℂ} {f : G D n → ℂ}, IsHeckeChar D χ → Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re →
    LeftInv (P D n ⊓ GF D n) f ∧
    (∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g, f (q * g) = f g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧ ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) f g q‖ ≤ u q := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.law_facts | exact GlobalTheory.CompanionTheory.ZUnf.law_facts | (intros; apply GlobalTheory.CompanionTheory.ZUnf.law_facts <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctionsStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_test_functions : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseTest.testEx | exact GlobalTheory.CompanionTheory.SW.BaseTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.BaseTest.testEx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximationStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_hermitian_local_approximation : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)), ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧ (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧ ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.exists_herm_at | exact GlobalTheory.CompanionTheory.Jp.exists_herm_at | (intros; apply GlobalTheory.CompanionTheory.Jp.exists_herm_at <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScalingStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)], ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d, νN.map (fun n : radN d => MulAut.conjNormal m n) = ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | exact GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

theorem smInt_zero_fun {X Z : Type} [MeasurableSpace X] [AddCommGroup Z] [Module ℂ Z]
    (μ : MeasureTheory.Measure X) (φ : X → Z) (h : ∀ x, φ x = 0) : smInt μ φ = 0 := by
  unfold smInt
  apply finsum_eq_zero_of_forall_eq_zero
  intro v
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hempty : φ ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hv (hx.symm.trans (h x))
    rw [hempty]
    simp

theorem mem_of_eq_mul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k))
    (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (h : HPG k i t) (β : Mir k (i + t)) (hβ : β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK)
    (e : uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β) :
    ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b' := by
  obtain ⟨y', _, b', hb', hβe⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_Bgrp.1 hβ
  obtain ⟨x, q, hx⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
  have e2 : uM k (i + t) y * levi k (i + t) g =
      uM k (i + t) (topV k i t x + ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y') *
        levi k (i + t) ((q : GL (Fin (i + t)) k) * b') := by
    calc uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β := e
      _ = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) *
            (uM k (i + t) y' * levi k (i + t) b') := by rw [hx, hβe]
      _ = _ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_mul_uM_levi _ _ _ _ _
  exact ⟨q, b', hb', (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_inj _ e2).2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ c K₁ hK b hb g hg
  have hz : ∀ v, fibV b g v = 0 := by
    intro v
    by_contra hne
    have hex : ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
        uM k (i + t) (midV k i t v) * levi k (i + t) g = (h : Mir k (i + t)) * β := by
      by_contra hno
      exact hne (hb _ hno)
    obtain ⟨h, β, hβ, e⟩ := hex
    exact hg (mem_of_eq_mul k i t c K₁ hK _ g h β hβ e)
  show clT τ W (smInt μ (fibV b g)) = 0
  rw [smInt_zero_fun μ _ hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEulerStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_rank_one_euler : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) → (∀ a : ℕ, 0 < a → ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤) ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitianStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle_hermitian : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | exact GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.BaseHasse.hasse <;> assumption)
end

