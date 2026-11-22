import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Formalism.LocalRingCardinality.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPureTensorsSeparateTensorProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.PureSep

theorem exists_finite_subspaces {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ W : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (W i)) ∧
      ∃ y : ⨂[ℂ] i, W i, PiTensorProduct.map (fun i => (W i).subtype) y = x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨fun i => ℂ ∙ m i, fun i => inferInstance,
      r • PiTensorProduct.tprod ℂ (fun i => (⟨m i, Submodule.mem_span_singleton_self _⟩ : ℂ ∙ m i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add a b ha hb =>
    obtain ⟨W₁, h₁, y₁, rfl⟩ := ha
    obtain ⟨W₂, h₂, y₂, rfl⟩ := hb
    refine ⟨fun i => W₁ i ⊔ W₂ i, fun i => by have := h₁ i; have := h₂ i; infer_instance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : W₁ i ≤ W₁ i ⊔ W₂ i)) y₁ +
        PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : W₂ i ≤ W₁ i ⊔ W₂ i)) y₂, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
      ← PiTensorProduct.map_comp]
    rfl

theorem exists_ellT_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  classical
  intro D V S M x hx
  obtain ⟨W, hW, y, rfl⟩ := exists_finite_subspaces x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  let ob : ∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (W τ))) ℂ (W τ) := fun τ =>
    haveI := hW τ; stdOrthonormalBasis ℂ (W τ)
  let B := Basis.piTensorProduct (fun τ => (ob τ).toBasis)
  obtain ⟨k, hk⟩ : ∃ k, B.repr y k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext k
    simp [h k]
  refine ⟨fun τ => ((ob τ (k τ) : W τ) : M.sm τ), ?_⟩
  have key : ∀ y' : ⨂[ℂ] τ, W τ,
      ellT M (fun τ => (((ob τ (k τ) : W τ) : M.sm τ) : M.H τ))
        (inclT M (PiTensorProduct.map (fun τ => (W τ).subtype) y')) = B.repr y' k := by
    intro y'
    induction y' using PiTensorProduct.induction_on with
    | smul_tprod r z =>
      unfold ellT inclT
      simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, Finsupp.smul_apply, B,
        Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, innerₛₗ_apply_apply, smul_eq_mul]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rfl
    | add a b ha hb =>
      simp only [map_add, Finsupp.add_apply] at ha hb ⊢
      rw [ha, hb]
  exact fun h => hk ((key y).symm.trans h)

end GlobalTheory.Mem.PureSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  first | exact @GlobalTheory.EvalAllRows.evalTranslate_norm_all | exact GlobalTheory.EvalAllRows.evalTranslate_norm_all | (intros; apply GlobalTheory.EvalAllRows.evalTranslate_norm_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlaceStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  first | exact @GlobalTheory.Mem.HD.RamBoth.ram_both | exact GlobalTheory.Mem.HD.RamBoth.ram_both | (intros; apply GlobalTheory.Mem.HD.RamBoth.ram_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorNotOverLevelPrimes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

theorem exists_hilbert_le_O (hR : RayField) (B : Base) (δ : FieldDat B.toPre) (hδ : δ.ray ≤ B.KsC) :
    ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn B.host.φ₀ ⊤ M ∧
      ∀ z ∈ M, IsIntegral ℤ z → ∃ y : B.O, B.embLL (B.OtoLL y) = z := by
  obtain ⟨M, hM⟩ := exists_isRayFieldIn B.host.φ₀ hR (𝔮 := ⊤) top_ne_bot
  refine ⟨M, hM, fun z hz hI => ?_⟩
  have hle : M ≤ δ.ray := RayMono.le_of_isRayFieldIn_of_dvd _ _ _ _ _ _ (natIdeal_ne_bot (modulus_ne_zero B.toPre))
    (Ideal.dvd_iff_le.2 le_top) hM δ.isRay
  obtain ⟨x, hx, rfl⟩ := B.mem_KsC.1 (hδ (hle hz))
  have hx' : IsIntegral ℤ x :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hI
  obtain ⟨y, hy⟩ := B.O_full x hx hx'
  exact ⟨y, by rw [hy]⟩

theorem twistConductor_not_over_levelPrimes (B : Base) (T : TwDat B) (w : B.places.Pl) {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : v ∈ T.Q w)
    (u : B.Word) (hp : (B.T u).Prime) : ¬ OverP B.host (B.T u) v := by
  intro ho
  obtain ⟨-, h1, -, h2⟩ := (T.psi_tw w).2.2.2 v fun h => ((T.psi_is w).ram v).1 h hv
  have := Examples₂.PlacesToy.prime_mem_unique v h1 hp (Ideal.absNorm_mem _) ho
  exact h2 (this ▸ .inr (.inr (.inr (.inr (.inl ⟨u, rfl⟩)))))

end GlobalTheory.Mem.HD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem addChar_pow_natCard_eq_one {A L : Type} [AddGroup A] [CommMonoid L] (ψ : AddChar A L) (c : A) :
    ψ c ^ Nat.card A = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem mem_Ks_of_pow_g (B : Base) (k : Fin 2) {x : B.LL} (hx : x ^ B.host.g k = 1) : x ∈ B.Ks := by
  have hp := B.host.g_prime k
  obtain ⟨z, hzK, hz⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
  have hne : B.host.g k * (B.host.g k - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (B.host.g k * (B.host.g k - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g k * (B.host.g k - 1)) := ⟨hne⟩
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_mul, hx, one_pow])
  rw [← hj]
  exact pow_mem hzK j

theorem chr0_mem_Ks : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I),
    ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  classical
  intro B px I p
  have hPr := (GlobalTheory.Mem.Col2.base_fields_primes_ok B px).2.1
  unfold chr0 P0 LevelP.ofLocal
  erw [MonoidHom.finset_prod_apply, Units.coe_prod]
  refine B.Ks.prod_mem fun PP _ => ?_
  have hk : ∃ k, PP.1 ∈ (B.primes px).vG k := by
    have h : PP.1 ∈ (B.primes px).vG 0 ∪ (B.primes px).vG 1 := by
      have h0 := PP.2
      unfold Formalism.L2.Col.Primes.vGs at h0
      convert h0
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hw⟩ := hk
  refine mem_Ks_of_pow_g B k ?_
  have hc : Nat.card (kP PP.1) = B.host.g k := by
    have h := hPr.vG_norm k PP.1 hw
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
    exact h
  rw [← hc]
  exact addChar_pow_natCard_eq_one _ _

end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftBound

variable {D : D7}

theorem entry_le (θ : InfF D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) (i j : Fin V.rank) :
    ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤ normInf θ V g := by
  unfold normInf
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j =>
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ j)

theorem norm_mM_le (θ : InfF D) (S T : HSp D) (a : GA D S) (b : GA D T) (p q : GlobalTheory.RealWeil.Ix S T) :
    ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ normInf θ S a * normInf θ T b := by
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  rw [GlobalTheory.RealWeil.mM_apply, GlobalTheory.RealWeil.blk, blockDiagonal_apply]
  split_ifs
  · rw [kroneckerMap_apply, transpose_apply, norm_mul, mul_comm]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) ha
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans (entry_le θ S a p.2 q.1.2 p.1.2)
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (entry_le θ T b p.2 p.1.1 q.1.1)
  · rw [norm_zero]
    exact mul_nonneg ha hb

theorem sum_mM_le (θ : InfF D) (S T : HSp D) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : GA D S) (b : GA D T),
    1 + ∑ p, ∑ q, ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ K * ((1 + normInf θ S a) * (1 + normInf θ T b)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Fintype.card (GlobalTheory.RealWeil.Ix S T) : ℝ) := ⟨_, rfl⟩
  have c0 : 0 ≤ c := hc ▸ Nat.cast_nonneg _
  refine ⟨1 + c * c, by positivity, fun a b => ?_⟩
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  have h1 : ∑ p, ∑ q, ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ c * (c * (normInf θ S a * normInf θ T b)) := by
    refine (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => norm_mM_le θ S T a b p q).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have h2 := mul_nonneg ha hb
  have h3 := mul_nonneg c0 c0
  nlinarith [mul_nonneg h3 ha, mul_nonneg h3 hb]

theorem one_add_normInf_mul (θ : InfF D) (V : HSp D) (g h : GA D V) :
    1 + normInf θ V (g * h) ≤ (1 + normInf θ V g) * (1 + normInf θ V h) := by
  have h1 := (GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V).1 g h
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) g
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h
  nlinarith

theorem om_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  intro D ψ hψ S T om hom θ hθ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨Ω, hosc, ⟨N, hN⟩, -⟩ :=
    GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.HM S T) GlobalTheory.RealWeil.HM_herm GlobalTheory.RealWeil.HM_det
      (GlobalTheory.RealWeil.BB ψ S T) (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.isHeis_rhoB h hψ) (GA D S × GA D T)
      (GlobalTheory.RealWeil.mM θ S T) (GlobalTheory.RealWeil.mM_unitary hθ)
  obtain ⟨K, hK0, hK⟩ := sum_mM_le θ S T
  obtain ⟨-, -, -, -, -, s6, s7, -⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ S
  obtain ⟨-, -, -, -, -, t6, t7, -⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ T
  refine ⟨N, fun f hf x y => ?_⟩
  obtain ⟨k, hk, a₀, ha₀, rfl⟩ := s7 x
  obtain ⟨k', hk', b₀, hb₀, rfl⟩ := t7 y
  have hf' := hom.om_pres (k, k') f hf
  have hF : IsThetaFunO ψ S T (GlobalTheory.RealWeil.toB hψ _ hf').1 := by
    rw [GlobalTheory.RealWeil.coe_toB]; exact hf'
  obtain ⟨C, hC⟩ := hN _ (GlobalTheory.RealWeil.sm_of_theta h hψ _ hF)
  refine ⟨|C| * (K * ((1 + normInf θ S a₀) * (1 + normInf θ T b₀))) ^ N, fun a ha b hb w => ?_⟩
  have haa := mul_mem ha₀ ha
  have hbb := mul_mem hb₀ hb
  obtain ⟨c, hc, hcF⟩ := GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hom Ω hosc _ haa _ hbb
  have e : ((k * a₀ * a, k' * b₀ * b) : GA D S × GA D T) = (a₀ * a, b₀ * b) * (k, k') := by
    rw [Prod.mk_mul_mk, s6 _ haa k hk, t6 _ hbb k' hk', mul_assoc, mul_assoc]
  have e2 := hcF _ hF
  rw [GlobalTheory.RealWeil.coe_toB] at e2
  rw [e, map_mul, Module.End.mul_apply, e2, Pi.smul_apply, norm_smul, hc, one_mul]
  refine (GlobalTheory.RealWeil.norm_ev_le w _).trans ((hC _).trans ?_)
  have n1 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a₀
  have n2 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b₀
  have n3 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have n4 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  have n5 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) (b₀ * b)
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ((hK _ _).trans ?_) N) (by positivity)
    (abs_nonneg C)
  rw [mul_assoc K]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  refine (mul_le_mul (one_add_normInf_mul θ S a₀ a) (one_add_normInf_mul θ T b₀ b) (by positivity)
    (by positivity)).trans_eq ?_
  ring

end GlobalTheory.Mem.LiftBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.GenZero

theorem exists_hasDerivAt_char (s : ℝ → ℂ) (hs : ∀ t t', s (t + t') = s t * s t') (h0 : s 0 = 1)
    (hc : ContinuousAt s 0) : ∃ m : ℂ, HasDerivAt s m 0 := by
  have hcont : Continuous s := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have e : s = fun t => s (t - t₀) * s t₀ := funext fun t => by rw [← hs, sub_add_cancel]
    rw [e]
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := s) (f := fun t => t - t₀) (by simpa using hc) (by fun_prop)
  let g : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..x, s y
  have hg : ∀ x, HasDerivAt g (s x) x := fun x => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨ε, hε⟩ : ∃ ε, g ε ≠ 0 := by
    by_contra hn
    push Not at hn
    have h1 : HasDerivAt g 0 0 := by
      rw [show g = fun _ => 0 from funext hn]
      exact hasDerivAt_const _ _
    have := (hg 0).unique h1
    rw [h0] at this
    exact one_ne_zero this
  have e : s = fun t => (g (t + ε) - g t) / g ε := by
    funext t
    rw [eq_div_iff hε]
    have h1 : g (t + ε) - g t = ∫ y in t..(t + ε), s y :=
      intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [h1]
    have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) s t
    rw [add_zero] at h2
    rw [← h2]
    simp only [hs, g]
    exact (intervalIntegral.integral_const_mul _ _).symm
  have h3 : HasDerivAt (fun t => g (t + ε)) (s (0 + ε)) 0 := HasDerivAt.comp_add_const 0 ε (hg _)
  exact ⟨_, ((h3.sub (hg 0)).div_const (g ε)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun e t)⟩

theorem lie_of_path {ι : Type} [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ) (m : ℝ → Matrix ι ι ℂ) (h0 : m 0 = 1)
    (hm : ∀ t, (m t)ᴴ * H * m t = H) (hX : ∀ k l, HasDerivAt (fun t => m t k l) (X k l) 0) :
    Xᴴ * H + H * X = 0 := by
  ext i j
  have h1 : HasDerivAt (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j)
      (∑ l, ((∑ k, star (X k i) * H k l) * m 0 l j + (∑ k, star (m 0 k i) * H k l) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      (HasDerivAt.fun_sum fun k _ => (hX k i).star.mul_const (H k l)).mul (hX l j)
  have e : (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j) = fun _ => H i j := by
    funext t
    rw [← congrFun (congrFun (hm t) i) j]
    simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  have h3 : (Xᴴ * H * m 0 + (m 0)ᴴ * H * X) i j = 0 := by
    rw [← h2]
    simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_add_distrib]
  rwa [h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h3

open scoped Classical

set_option maxHeartbeats 1000000 in
open GlobalTheory.RealWeil in

theorem exists_generator : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  intro D θ σ h ψ hψ S T om hw hc γ hγ hadd hinf X hX
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := γ 0) (by rw [← this, mul_one])
  have hH := isHeis_rhoB (S := S) (T := T) h hψ
  have hL := lie_of_path (HM S T) X (fun t => mM θ S T (γ t)) (by simp only [hγ0, map_one])
    (fun t => mM_unitary h.inf _) hX
  obtain ⟨κ, _, c, p, q, hq, hn⟩ := GlobalTheory.Mem.Lift.Normal.normal_quad (Ix S T) (HM S T) X HM_herm HM_det hL
  obtain ⟨Ω, hΩ, -, hd⟩ := GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) hH
    (GA D S × GA D T) (mM θ S T) (mM_unitary h.inf)
  obtain ⟨lam, hlam⟩ := hd γ X hγ0 hX κ c p q hq
  have sm := sm_of_theta (S := S) (T := T) h hψ
  choose s hs1 hs using fun t => GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hw Ω hΩ (γ t).1 (hinf t).1 (γ t).2 (hinf t).2
  replace hs : ∀ t (F : BB ψ S T), IsThetaFunO ψ S T F.1 → om (γ t) F.1 = s t • ((Ω (γ t) F).1 : WO S T → ℂ) := hs
  obtain ⟨-, hsmul, hsm, hone, hmul, -⟩ := hΩ
  have cs : ∀ (a : ℂ) (G : BB ψ S T), ((a • G).1 : WO S T → ℂ) = a • (G.1 : WO S T → ℂ) := fun _ _ => rfl
  have hne : ∀ t, s t ≠ 0 := fun t e => by simpa [e] using hs1 t
  have hD : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      HasDerivAt (fun t => Ω (γ t) F) (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F) 0 := fun F hF =>
    hn _ _ hH F (sm F hF) ▸ hlam F (sm F hF)
  by_cases hex : ∃ F₀ : BB ψ S T, IsThetaFunO ψ S T F₀.1 ∧ F₀ ≠ 0
  swap
  · push Not at hex
    refine ⟨lam, fun F hF => ⟨fun t => Ω (γ t) F, fun t => ?_, hD F hF⟩⟩
    have e : Ω (γ t) F = 0 := by
      have := hsmul (γ t) 0 F (sm F hF)
      rw [zero_smul, zero_smul] at this
      exact (congrArg (Ω (γ t)) (hex F hF)).trans this
    rw [hs t F hF]
    beta_reduce
    rw [e]
    exact (smul_zero _).symm
  obtain ⟨F₀, hF₀, hne₀⟩ := hex
  have hΩne : ∀ g, Ω g F₀ ≠ 0 := by
    intro g e
    have h1 := hmul g⁻¹ g F₀ (sm _ hF₀)
    have h2 := hsmul g⁻¹ 0 F₀ (sm _ hF₀)
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone _ (sm _ hF₀), e, h2] at h1
    exact hne₀ h1
  have hth : ∀ t, IsThetaFunO ψ S T (Ω (γ t) F₀).1 := by
    intro t
    have h1 := (thetaSub ψ S T).smul_mem (s t)⁻¹ (hw.om_pres (γ t) _ hF₀)
    rw [hs t F₀ hF₀, smul_smul, inv_mul_cancel₀ (hne t), one_smul] at h1
    exact h1
  have hms : ∀ t t', s (t + t') = s t * s t' := by
    intro t t'
    have h1 := hs (t + t') F₀ hF₀
    rw [hadd, map_mul, Module.End.mul_apply, hs t' F₀ hF₀, map_smul, hs t _ (hth t'), ← hmul _ _ _ (sm _ hF₀),
      smul_smul] at h1
    have h2 : (s t' * s t) • Ω (γ t * γ t') F₀ = s (t + t') • Ω (γ t * γ t') F₀ := QB_ext fun x => by
      rw [cs, cs, h1]
    rw [← smul_left_injective ℂ (hΩne _) h2, mul_comm]
  have hs0 : s 0 = 1 := by
    have := hms 0 0
    rw [add_zero] at this
    exact mul_left_cancel₀ (hne 0) (by rw [← this, mul_one])
  obtain ⟨w, hw₀⟩ : ∃ w, (F₀.1 : WO S T → ℂ) w ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hne₀ (QB_ext hn')
  have hcs : ContinuousAt s 0 := by
    have h1 : ContinuousAt (fun t => ev _ _ w (Ω (γ t) F₀)) 0 :=
      (ev _ _ w).continuous.continuousAt.comp (hD F₀ hF₀).continuousAt
    have h2 : ev _ _ w (Ω (γ 0) F₀) ≠ 0 := by
      rw [hγ0, hone _ (sm _ hF₀), ev_apply]
      exact hw₀
    have h3 : ContinuousAt (fun t => om (γ t) F₀.1 w) 0 := ((hc _ hF₀ w).comp hγ).continuousAt
    refine (h3.div h1 h2).congr ?_
    filter_upwards [h1.eventually_ne h2] with t ht
    rw [Pi.div_apply, div_eq_iff ht, hs t F₀ hF₀, ev_apply]
    rfl
  obtain ⟨m, hm⟩ := exists_hasDerivAt_char s hms hs0 hcs
  refine ⟨lam + m, fun F hF => ⟨fun t => s t • Ω (γ t) F, fun t => (cs _ _).trans (hs t F hF).symm, ?_⟩⟩
  have h1 := hm.smul (hD F hF)
  rw [hs0, one_smul, hγ0, hone _ (sm _ hF)] at h1
  rw [add_smul, ← add_assoc]
  exact h1

end GlobalTheory.Mem.Lift.GenZero

end
end

