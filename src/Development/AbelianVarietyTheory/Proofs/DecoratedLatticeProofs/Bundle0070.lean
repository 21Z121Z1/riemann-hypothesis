import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0056
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EquivariantHomMultiplicityFreeIrreducibleStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantHom_multiplicityFree_irreducible : ∀ (G H J : Type) [Group G] [Group H] [DecidableEq J] (A B : J → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)] [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, FiniteDimensional ℂ (A j)] [∀ j, FiniteDimensional ℂ (B j)] (α : ∀ j, Representation ℂ G (A j)) (β : ∀ j, Representation ℂ H (B j)), (∀ j, (α j).IsIrreducible) → (∀ j, (β j).IsIrreducible) → (∀ j j', Nonempty ((α j).Equiv (α j')) → j = j') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ω : Representation ℂ (G × H) W), Nonempty ((Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H)) ((β j).comp (MonoidHom.snd G H))).Equiv ω) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible → ∀ S : Submodule ℂ (V →ₗ[ℂ] W), (∀ T ∈ S, ∀ g v, T (ρ g v) = ω (g, 1) (T v)) → (∀ T ∈ S, ∀ h, ω (1, h) ∘ₗ T ∈ S) → S ≠ ⊥ → ∀ Q : V →ₗ[ℂ] W, (∀ g v, Q (ρ g v) = ω (g, 1) (Q v)) → Q ∈ S := by
  first | exact @GlobalTheory.EquivHomIrr.equivariantHom_mem_of_stable | exact GlobalTheory.EquivHomIrr.equivariantHom_mem_of_stable | (intros; apply GlobalTheory.EquivHomIrr.equivariantHom_mem_of_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocksStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_piTensorMvPolynomialEquiv_blocks : ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  first | exact @GlobalTheory.BlockPoly.exists_blockEquiv | exact GlobalTheory.BlockPoly.exists_blockEquiv | (intros; apply GlobalTheory.BlockPoly.exists_blockEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_identities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  first | exact @GlobalTheory.KJInf.substIdentities | exact GlobalTheory.KJInf.substIdentities | (intros; apply GlobalTheory.KJInf.substIdentities <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianSelfDualMaxSlope
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.IntegralDualSlope

variable {K : Type} [Field K] [NumberField K]

noncomputable def coordDual {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) :=
  (Formalism.HN.dualLat M).map
    ((Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap.restrictScalars (𝓞 K))

omit [NumberField K] in

theorem coords_dotProduct {n : ℕ} (f : Module.Dual K (Fin n → K)) (x : Fin n → K) :
    (Pi.basisFun K (Fin n)).dualBasis.equivFun f ⬝ᵥ x = f x := by
  conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x, map_sum]
  simp [dotProduct, mul_comm]

theorem dotProduct_mem_one {n : ℕ} {M : Submodule (𝓞 K) (Fin n → K)} {y : Fin n → K}
    (hy : y ∈ coordDual M) : ∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨f, hf, rfl⟩ := hy
  intro x hx
  obtain ⟨a, ha⟩ := hf x hx
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [ha]
  exact (coords_dotProduct f x).symm

theorem coordDual_spec [StarRing K] [IsTotallyComplex K] {n : ℕ} (hn : 0 < n)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det) :
    (coordDual M).FG ∧ coordDual M ≠ ⊥ ∧
      Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) (coordDual M) =
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X)
          (Formalism.HN.dualLat M) := by
  have hfg := Formalism.HN.DualPolygon.dualLat_fg M hM.span_eq_top
  have hinj : Function.Injective (Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap :=
    (Pi.basisFun K (Fin n)).dualBasis.equivFun.injective
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h := hM.span_eq_top
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h
    exact bot_ne_top h
  refine ⟨hfg.map _, fun h => ?_, ?_⟩
  · refine Formalism.HN.DualPolygon.dual_ne_bot (Pi.basisFun K (Fin n)) M hM.fg hM.span_eq_top hM0 ?_
    refine (Submodule.eq_bot_iff _).2 fun f hf => hinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ (Submodule.mem_map_of_mem hf)
  · have hu := Formalism.HN.DualPolygon.dualFrame_unit X hX
    have := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X)
      (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) _ hu hu hinj (fun v x => by
        unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
        simp) _ hfg).2.2.2.1
    unfold Formalism.HN.muMaxDef coordDual
    rw [this]

theorem muMaxDual_nonpos :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
      IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      IsRatHerm K0 H X → ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → 0 < n → (Formalism.L2.DIV.toHLat X M).muMaxDual ≤ 0 := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n H X hH M hM hle hn
  have hX : ∀ v, IsUnit (X v).det := fun v => (hH.2 v).1
  obtain ⟨hfg, hne, heq⟩ := coordDual_spec hn M hM X hX
  obtain ⟨hherm, hdet, -⟩ := GlobalTheory.ratHerm_herm_unit_aniso K K0 v0 hv0 n 0 H X hH
  have hG := GlobalTheory.isRatHerm_dualFrame K K0 n H X hH
  have hint := GlobalTheory.DualInt.dual_form_integral K n H hherm hdet M hle
  have key := GlobalTheory.muMax_nonpos_of_lcv_nonneg K (Formalism.L2.DIV.toHLat (Formalism.HN.dualFrame X) (coordDual M))
    (Formalism.HN.DualPolygon.dualFrame_unit X hX) hfg hne (fun N hN _ => by
      have hNfg : Submodule.FG (N : Submodule (𝓞 K) (Fin n → K)) :=
        (hfg.of_le hN)
      exact GlobalTheory.T.hermitian_lattice_covolume_nonneg K K0 hK0 v0 hv0 n _ _ hG N hNfg (fun y hy y' hy' =>
        hint y y' (dotProduct_mem_one (hN hy)) (dotProduct_mem_one (hN hy'))))
  exact heq.symm.trans_le key

end GlobalTheory.IntegralDualSlope
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntMemInverseHalfDifferent
section
open NumberField Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.DgenNe

theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have h1 : H.sigmaOf g = H.sigmaOf g' :=
    AlgEquiv.ext fun x => H.φ₀.injective (RingHom.congr_fun h x)
  exact (H.gal).symm.injective h1

theorem embT_injective {R : Ranks} (H : Host R) : Function.Injective (embT H) := fun τ τ' h =>
  Subtype.ext (emb_injective H h)

theorem bb_ne_bot {R : Ranks} (H : Host R) : H.𝔟 ≠ ⊥ := by
  intro h
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem int_mem_inverse_half_different {R : Ranks} (H : Host R) (t : 𝓞 H.E) :
    ((t : H.E)) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  have h0 : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (bb_ne_bot H)
  have h1 : (1 : H.E) ∈ H.AA0 := by
    unfold Host.AA0
    rw [FractionalIdeal.mem_inv_iff h0]
    intro y hy
    obtain ⟨x, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [one_mul]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
  have h2 : t • (1 : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := Submodule.smul_mem _ t h1
  simpa [Algebra.smul_def] using h2

end GlobalTheory.Mem.Col2.DgenNe

namespace GlobalTheory.Mem.Col2.DgenNe

theorem dgen_ne_zero : ∀ {R : Ranks} (H : Host R) (cD : Tau R → ℂ), Th.IsDgen H (embT H) cD → ∀ τ, cD τ ≠ 0 := by
  intro R H cD hD τ hτ
  classical
  obtain ⟨M, hM, hemb, hgen⟩ := hD
  obtain ⟨s, hs, hell⟩ := hgen τ
  have hs0 : s = 0 := Subtype.ext (hs.trans hτ)
  rw [hs0, Submodule.span_zero_singleton] at hell
  let e : Tau R → H.E →+* M := fun σ => (embT H σ).codRestrict M (hemb σ)
  have hlift : ∀ σ (x : H.E), Formalism.MainNotions.TaylorLogMetric.liftM M (embT H σ x) = e σ x := by
    intro σ x
    simp only [Formalism.MainNotions.TaylorLogMetric.liftM, dif_pos (hemb σ x)]
    rfl
  let f : Tau R → (𝓞 H.E →* M) := fun σ => ((e σ).comp (algebraMap (𝓞 H.E) H.E)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective H
    have h2 : e σ = e σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 H.E))
      (RingHom.ext fun x => DFunLike.congr_fun h x)
    ext x
    exact congrArg Subtype.val (RingHom.congr_fun h2 x)
  have hli := (linearIndependent_monoidHom (𝓞 H.E) M).comp f hf
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  let N := Th.mmM H (embT H) M
  let P : Submodule M (Tau R → M) :=
    { carrier := {v | ∃ b : 𝓞 M, b ≠ 0 ∧ b • v ∈ N}
      add_mem' := by
        rintro v w ⟨b, hb, hv⟩ ⟨b', hb', hw⟩
        refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
        have : (b * b') • (v + w) = b' • (b • v) + b • (b' • w) := by
          rw [smul_add, mul_smul, mul_smul, smul_comm b b' v]
        rw [this]
        exact N.add_mem (N.smul_mem _ hv) (N.smul_mem _ hw)
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro m v ⟨b, hb, hv⟩
        obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) m
        have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
        have hy1 : algebraMap (𝓞 M) M y ≠ 0 := by
          intro h0
          exact hy0 (IsFractionRing.injective (𝓞 M) M (by rw [h0, map_zero]))
        refine ⟨y * b, mul_ne_zero hy0 hb, ?_⟩
        have : (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) • v) = x • (b • v) := by
          funext σ
          change (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) * v σ) = x • (b • v σ)
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
          field_simp
        rw [this]
        exact N.smul_mem _ hv }
  have hP : ∀ t : 𝓞 H.E, (fun σ => e σ t) ∈ P := fun t =>
    ⟨1, one_ne_zero, by
      rw [one_smul]
      exact Submodule.subset_span ⟨(t : H.E), int_mem_inverse_half_different H t, funext fun σ => (hlift σ t).symm⟩⟩
  have hsingle : (Pi.single τ 1 : Tau R → M) ∈ P := by
    have hle : Submodule.span M (Set.range (flip ((fun g : 𝓞 H.E →* M => (g : 𝓞 H.E → M)) ∘ f))) ≤ P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact hP t
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨b, hb, hbN⟩ := hsingle
  have hmem : algebraMap (𝓞 M) M b ∈ Th.ellT H (embT H) M τ := by
    rw [Th.ellT, Submodule.mem_comap]
    convert hbN using 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp [Algebra.smul_def]
    · simp [h]
  rw [hell, Submodule.mem_bot] at hmem
  exact hb (IsFractionRing.injective (𝓞 M) M (by rw [hmem, map_zero]))

end GlobalTheory.Mem.Col2.DgenNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlaceStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_tprod_of_commute_at_each_place : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V W : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (R : ∀ τ, Set ((V τ →ₗ[ℂ] V τ) × (W τ →ₗ[ℂ] W τ))) (Q : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W), (∀ τ, ∀ p ∈ R τ, Q ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) = PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2) ∘ₗ Q) → Q ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧ T = PiTensorProduct.map t} := by
  first | exact @GlobalTheory.PiTensorCommute.mem_span_map_of_commute | exact GlobalTheory.PiTensorCommute.mem_span_map_of_commute | (intros; apply GlobalTheory.PiTensorCommute.mem_span_map_of_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NodesOfSizeData
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Diag.PG

noncomputable section

namespace GlobalTheory.Diag.PG.NodeParameters

theorem y_ge {eps x : ℝ} (he : 0 < eps) (hx : (4 + 18 / eps) ^ (3 / eps) ≤ x) :
    4 + 18 / eps ≤ x ^ (eps / 3) := by
  have h0 : 0 ≤ 4 + 18 / eps := by positivity
  calc 4 + 18 / eps = ((4 + 18 / eps) ^ (3 / eps)) ^ (eps / 3) := by
        rw [← Real.rpow_mul h0]
        have : 3 / eps * (eps / 3) = 1 := by field_simp
        rw [this, Real.rpow_one]
    _ ≤ x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)

theorem xeps_eq {eps x : ℝ} (hx : 0 ≤ x) : x ^ eps = (x ^ (eps / 3)) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

theorem logx_le' {eps x : ℝ} (he : 0 < eps) (hx : 0 ≤ x) : Real.log x ≤ 3 * x ^ (eps / 3) / eps := by
  have := Real.log_le_rpow_div hx (by positivity : 0 < eps / 3)
  calc _ ≤ _ := this
    _ = _ := by field_simp

theorem poly {eps y : ℝ} (he : 0 < eps) (hy : 4 + 18 / eps ≤ y) :
    2 + 2 * y + 6 * (3 * y / eps) ≤ y ^ 3 ∧ 2 + 5 * (3 * y / eps) ≤ y ^ 3 := by
  have hq : 0 ≤ 18 / eps := by positivity
  have h1 : 1 ≤ y := by linarith
  have h2 : y * (4 + 18 / eps) ≤ y ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hy (by linarith)
  have h3 : y ^ 2 ≤ y ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  have e1 : 6 * (3 * y / eps) = y * (18 / eps) := by ring
  have e2 : 5 * (3 * y / eps) = y * (15 / eps) := by ring
  have h4 : y * (15 / eps) ≤ y * (18 / eps) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by norm_num) he.le) (by linarith)
  have h5 : 0 ≤ y * (18 / eps) := by positivity
  rw [e1, e2]
  constructor <;> nlinarith

theorem exp_big {eps x : ℝ} (he : 0 < eps) (hx1 : 1 ≤ x) (hx : (4 + 18 / eps) ^ (3 / eps) ≤ x) :
    4 * Real.exp (x ^ (eps / 3)) ^ 2 * x ^ 6 ≤ Real.exp (x ^ eps) ∧
      3 * x ^ 5 ≤ Real.exp (x ^ eps) := by
  have hx0 : 0 < x := by linarith
  have hyg := y_ge he hx
  obtain ⟨p1, p2⟩ := poly he hyg
  have hl := logx_le' he hx0.le
  have hxe : x ^ eps = (x ^ (eps / 3)) ^ 3 := xeps_eq hx0.le
  rw [hxe]
  set y := x ^ (eps / 3) with hy
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith
  have ex : x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
  constructor
  · calc 4 * Real.exp y ^ 2 * x ^ 6 ≤ Real.exp 2 * Real.exp y ^ 2 * Real.exp (Real.log x) ^ 6 := by
          rw [← ex]; gcongr
      _ = Real.exp (2 + 2 * y + 6 * Real.log x) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (y ^ 3) := Real.exp_le_exp.2 (by nlinarith)
  · calc 3 * x ^ 5 ≤ Real.exp 2 * Real.exp (Real.log x) ^ 5 := by
          rw [← ex]; gcongr
      _ = Real.exp (2 + 5 * Real.log x) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (y ^ 3) := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.Diag.PG.NodeParameters

namespace GlobalTheory.Diag.PG.NodeParameters

theorem w''_eq {D : D7} (L : SizeData₂ D) : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
  unfold Scale.w'' Scale.b' Scale.a
  field_simp

theorem top_real {x b a c k aT bT bp b1 u1 uk s : ℝ} (hx1 : 1 ≤ x) (hb1 : 1 ≤ b) (ha : a = x * b) (hc : 1 ≤ c)
    (hk : 3 ≤ k) (hk5 : k ≤ x ^ 5) (hB : 3 * x ^ 5 ≤ b) (hs : s ≤ b)
    (hu1 : u1 = aT + (k - 1) / 2) (huk : uk = -bT - (k - 1) / 2)
    (haT : a ≤ aT ∧ aT ≤ a + a / c) (hbT : bp ≤ bT) (hbp : 0 ≤ bp)
    (hb1t : b1 - bT > (k - 1) / 2 + 3) (hb1e : b1 = bT + ((⌊bp / x⌋ : ℤ) : ℝ)) :
    s ≤ u1 ∧ u1 ≤ b ^ 2 ∧ 3 ≤ b1 + uk ∧ b1 / 2 ≤ -uk := by
  have hb0 : 0 ≤ b := by linarith
  have hx0 : 0 ≤ x := by linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hab : b ≤ a := by rw [ha]; exact le_mul_of_one_le_left hb0 hx1
  have hdiv : a / c ≤ a := div_le_self ha0 hc
  have hfl : ((⌊bp / x⌋ : ℤ) : ℝ) ≤ bp / x := Int.floor_le _
  have hbx : bp / x ≤ bp := div_le_self hbp hx1
  have hx5 : x ≤ x ^ 5 := by
    have := pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5); simpa using this
  have h1 : x * b ≤ x ^ 5 * b := mul_le_mul_of_nonneg_right hx5 hb0
  have h2 : x ^ 5 ≤ x ^ 5 * b := le_mul_of_one_le_right (by positivity) hb1
  have h3 : 3 * x ^ 5 * b ≤ b * b := mul_le_mul_of_nonneg_right hB hb0
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hs, hab, haT.1, hu1, hk]
  · rw [sq]
    linarith only [hu1, haT.2, hdiv, ha, h1, h2, h3, hk5, hk]
  · linarith only [hb1t, huk]
  · linarith only [hb1e, hfl, hbx, hbT, huk, hk]

theorem node_real {bj ej w eta t x s : ℝ} (hw : w ≤ ej) (hc : -eta ≤ bj - ej) (ht : 1 ≤ t) (he : 0 < eta)
    (hte : t * eta ≤ w / x) (hx2 : 2 ≤ x) (hw0 : 0 < w) (hs : s ≤ w / 2) : s ≤ bj := by
  have h1 : eta ≤ t * eta := le_mul_of_one_le_left he.le ht
  have h2 : w / x ≤ w / 2 := div_le_div_of_nonneg_left hw0.le two_pos hx2
  linarith only [hw, hc, h1, h2, hte, hs]

theorem nodes_of_parameters : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D)
    (_ : ParameterChoice' D L), SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → Nodes D L.sc.x eps := by
  intro eps he he52
  refine ⟨max 2 ((4 + 18 / eps) ^ (3 / eps)), ?_⟩
  intro D L P hS heps hx
  subst heps
  have hx2 : 2 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hxb : (4 + 18 / L.sc.eps) ^ (3 / L.sc.eps) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨hN, -, hK, -, hT, -, -, -, -, -, -, -, -, hEta, -, -, -, -, hBm, -⟩ := hS
  obtain ⟨hA, hB⟩ := exp_big he (by linarith) hxb
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hbdef : bx L.sc.x L.sc.eps = L.sc.b := rfl
  have hbe : Real.exp (L.sc.x ^ L.sc.eps) = L.sc.b := rfl
  have hXe : Real.exp (L.sc.x ^ (L.sc.eps / 3)) = L.sc.X' := rfl
  rw [hbe] at hA hB
  rw [hXe] at hA
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb0 : 0 < L.sc.b := by linarith
  have hX0 : 0 < L.sc.X' := by unfold Scale.X'; positivity
  have hn0 : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this

  have hth : szTh L = L.sc.eps / 100 := rfl
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    have h := hN.2
    rw [hth] at h
    have e := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 2 + 8 * L.sc.eps + L.sc.eps / 100 ≤ (3 : ℝ))
    have e3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ (3 : ℕ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e3] at e
    exact le_trans h e
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    have h := hK.2
    rw [hth] at h
    have e := Real.rpow_le_rpow_of_exponent_le hx1
      (by linarith : 9 / 2 + 10 * L.sc.eps + L.sc.eps / 100 ≤ (5 : ℝ))
    have e5 : L.sc.x ^ (5 : ℝ) = L.sc.x ^ (5 : ℕ) := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e5] at e
    exact le_trans h e

  have hw0 := S.w''_pos L
  have hsq : Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n / 2 := by
    have hw := w''_eq L
    have hn6 : (D.R.n : ℝ) ^ 2 ≤ L.sc.x ^ 6 := by
      have := pow_le_pow_left₀ hn0.le hn3 2
      rw [← pow_mul] at this; simpa using this
    have h4 : 4 * L.sc.X' ^ 2 * (D.R.n : ℝ) ^ 2 ≤ L.sc.b := by
      have : 4 * L.sc.X' ^ 2 * (D.R.n : ℝ) ^ 2 ≤ 4 * L.sc.X' ^ 2 * L.sc.x ^ 6 :=
        mul_le_mul_of_nonneg_left hn6 (by positivity)
      linarith
    have hw0' : 0 ≤ L.sc.w'' D.R.n / 2 := by positivity
    rw [← Real.sqrt_sq hw0']
    apply Real.sqrt_le_sqrt
    rw [hw, div_div, div_pow, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h4 hb0.le
    nlinarith
  have hwb := S.w''_le_b L
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk3r : (3 : ℝ) ≤ D.R.k := by exact_mod_cast hk3
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_⟩
  ·
    intro τ j
    refine ⟨?_, L.b_le τ j⟩
    have hwj := S.wj_ge L τ (j.1 + 1) (by omega) (by omega)
    have e : wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
      have : j.1 + 1 - 1 < D.R.m := by omega
      simp only [wj, dif_pos this]
      rfl
    rw [e] at hwj
    have hc := abs_le.1 (L.be_close τ j j)
    push_cast at hc
    rw [hbdef]
    exact node_real hwj hc.1 hT.1 L.etaSz_pos hEta.2.2.2.1 hx2 hw0 hsq
  ·
    intro τ
    exact hBm τ hm0
  ·
    rintro τ ⟨t, ht⟩
    have hk0 : 0 < D.R.k := by omega
    obtain ⟨hu1, huk⟩ := L.top_u τ t hk0 ht
    have hden : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by
      have h1 : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx1 (by unfold Scale.A; norm_num)
      have h2 : (1 : ℝ) ≤ D.R.k := by linarith
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ _ := mul_le_mul h2 h1 zero_le_one (by linarith)
    have hb'0 : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.b Scale.X'; positivity
    rw [hbdef]
    exact top_real hx1 hb1 rfl hden hk3r hk5 hB (le_trans hsq (by linarith)) hu1 huk (L.aT_win t) (L.bT_ge t) hb'0
      (L.top_b τ t hm0 ht) (P.topPlace_first_bound τ t hm0 ht)

end GlobalTheory.Diag.PG.NodeParameters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ), FiniteDimensional ℂ (Vn lam n) ∧ ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ), ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := by
  first | exact @GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem | exact GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem | (intros; apply GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorUnitIndexIrreducibleUnStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary : ∀ (a : ℕ), 0 < a → ∀ (lam : Unit → DomWeight a) (n : Unit → ℕ), Vn lam n ≠ ⊥ ∧ ∀ U : Submodule ℂ (PY Unit a), U ≤ Vn lam n → (∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U) → U = ⊥ ∨ U = Vn lam n := by
  first | exact @GlobalTheory.KJInf.Vn_unit_irreducible | exact GlobalTheory.KJInf.Vn_unit_irreducible | (intros; apply GlobalTheory.KJInf.Vn_unit_irreducible <;> assumption)
end

