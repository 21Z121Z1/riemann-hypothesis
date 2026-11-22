import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0202
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0210
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvIoPi
section
namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.MemLoc GlobalTheory.ThetaTie
open scoped Formalism.Per

theorem exists_inv_io_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  intro l _ P AI T
  obtain ⟨-, -, hun, hth, -⟩ := thetaD_props l
  have hθ : Per.θ l AI.π₁ ≠ 0 := by
    have h : Per.θ l AI.π₁ = PreTilt.untilt AI.ε1 - 1 := by
      rw [LocAinf.π₁, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
    rw [h]
    exact sub_ne_zero.2 (isEps AI).2
  have hne : Per.θD l (aDp l AI.π₁) ≠ 0 := by
    rw [hth]
    exact fun h0 => hθ (Subtype.ext h0)
  obtain ⟨v, hv⟩ := (hun _ hne).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v),
    (fil_zero T _).2 ⟨v, (T.eD.apply_symm_apply _).symm⟩, T.eD.injective ?_⟩
  rw [map_mul, io_apply, eD_ιA, T.eD.apply_symm_apply, ← map_mul, hv, map_one, map_one]

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJordanHolderThroughLine
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models.ThroughLine

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (K : Ob k G) (f : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A f ∧ Function.Injective f ∧ Function.Exact f p := by
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) (fun g x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hp g x, LinearMap.mem_ker.mp hx, map_zero]))
  refine ⟨K, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (LinearMap.ker p).subtype_injective.comp e.symm.injective, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [← he]
    simp
  · exact ⟨e ⟨y, hy⟩, by simp⟩
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact j q := by
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) (fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨A.ρ g y, hj g y⟩))
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => he g (Submodule.Quotient.mk x),
    e.surjective.comp (LinearMap.range j).mkQ_surjective, fun y => ?_⟩
  simp [Submodule.Quotient.mk_eq_zero]

theorem simple_chr (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have h : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule k (Fin 1 → k)) (congrArg Subrepresentation.toSubmodule h')
  · rcases eq_bot_or_eq_top S.toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.toSubmodule_injective h')
    · exact Or.inr (Subrepresentation.toSubmodule_injective h')

theorem sameSS_three {s t u : ℕ} {M : Type} [AddCommGroup M] [Module k M] {π : Representation k G M}
    (C : (Fin s ⊕ Unit) ⊕ Fin t → Ob k G) (e : Fin u ≃ (Fin s ⊕ Unit) ⊕ Fin t)
    (h : SameSS π (((piRep fun a => (C (.inl (.inl a))).ρ).prod (C (.inl (.inr ()))).ρ).prod
      (piRep fun a => (C (.inr a)).ρ))) : SameSS π (piRep fun a => (C (e a)).ρ) := by
  have h1 : SameSS π (piRep fun a => (C a).ρ) := by
    refine h.congr_right
      ((((LinearEquiv.refl k _).prodCongr (LinearEquiv.piUnique k (fun a : Unit => Fin (C (.inl (.inr a))).m → k)).symm).trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s) Unit (fun a => Fin (C (.inl a)).m → k)).symm).prodCongr
          (LinearEquiv.refl k _) |>.trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s ⊕ Unit) (Fin t) (fun a => Fin (C a).m → k)).symm) ?_
    intro g x
    funext a
    rcases a with (a | a) | a <;> rfl
  refine h1.congr_right (LinearEquiv.piCongrLeft k (fun a => Fin (C a).m → k) e).symm ?_
  intro g x
  rfl

end GlobalTheory.Models.ThroughLine

open GlobalTheory.Models.ThroughLine in

theorem GlobalTheory.Models.ModTh.exists_jordanHolder_through_line : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  intro k G _ _ l n _ _ _ R F r Dt M B A₁ χ j p N hN hj hji hp hps
  obtain ⟨K, f, hf, hfi, hfe⟩ := exists_ker A₁ (chr χ) p hp
  obtain ⟨Q, q, hq, hqs, hqe⟩ := exists_coker A₁ B j hj
  have hA := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ B j N hj hji hN
  have hK := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M K A₁ f _ hf hfi hA
  have hL := GlobalTheory.Models.ModTh.model_push_of_surjective F M A₁ (chr χ) p _ hp hps hA
  have hQ := GlobalTheory.Models.ModTh.model_push_of_surjective F M B Q q _ hq hqs hN
  obtain ⟨s, C, L, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M K _ hK
  obtain ⟨t, C', L', d1, d2, d3, d4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M Q _ hQ
  obtain ⟨oB, lB, -, cB⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
  obtain ⟨oA, lA, -, cA⟩ := GlobalTheory.T.obj_and_abc_of_model F M A₁ _ hA
  let S : (Fin s ⊕ Unit) ⊕ Fin t → Σ A : Ob k G, Lats k n A.m :=
    Sum.elim (Sum.elim (fun a => ⟨C a, L a⟩) fun _ => ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩)
      fun a => ⟨C' a, L' a⟩
  let e := (Fintype.equivFin ((Fin s ⊕ Unit) ⊕ Fin t)).symm
  have hfl : ∀ m : ℕ, IsFiniteLength k (Fin m → k) := fun m =>
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨_, fun a => (S (e a)).1, fun a => (S (e a)).2, e.symm (.inl (.inr ())), fun a => ?_, fun a => ?_,
    ?_, fun i x => ?_, ?_⟩
  · show M.Model (S (e a)).1 (S (e a)).2
    rcases e a with (b | b) | b
    exacts [c1 b, hL, d1 b]
  · show IsSimpleModule (MonoidAlgebra k G) (S (e a)).1.ρ.asModule
    rcases e a with (b | b) | b
    exacts [c2 b, simple_chr χ, d2 b]
  · refine sameSS_three (fun a => (S a).1) e ?_
    exact (SameSS.of_exact hj hq hji hqs hqe (hfl _)).trans
      (((SameSS.of_exact hf hp hfi hps hfe (hfl _)).trans (c3.prod (SameSS.refl _ (hfl _)))).prod d3)
  · rw [Equiv.sum_comp e (fun a => sen ((F.D (S a).1).γ i) ((S a).2 i) x), Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit),
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B Q j q N oB hj hq hji hqs hqe i (lB i) (cB i) x,
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ (chr χ) f p _ oA hf hp hfi hps hfe i (lA i) (cA i) x, c4, d4]
    rfl
  · show S (e (e.symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemTameDescentClassEqOfPowMem
section
noncomputable section

namespace GlobalTheory.LcImage

open PowerSeries GlobalTheory.BK GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem norm_intCast_eq_one {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] {u : ℤ} (hu : ¬ (l : ℤ) ∣ u) : ‖(u : K)‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one u)
    (not_lt.1 fun h => hu (Padic.norm_intCast_lt_one_iff.1 h))

theorem exists_mul_intCast_eq {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {r : ℤ} (hr : r ≠ 0)
    {m : ℕ} (hm : padicValInt l r ≤ m) : ∃ t : O, algebraMap O K t * (r : K) = (l : K) ^ m := by
  obtain ⟨v, hvdef⟩ : ∃ v, padicValInt l r = v := ⟨_, rfl⟩
  have hdv := padicValInt_dvd (p := l) r
  rw [hvdef] at hdv hm
  obtain ⟨u, hu⟩ := hdv
  have hpr : (l : ℕ).Prime := Fact.out
  have hu' : ¬ (l : ℤ) ∣ u := by
    rintro ⟨k, rfl⟩
    have h := (padicValInt_dvd_iff (p := l) (v + 1) r).1
      ⟨k, by rw [hu, pow_succ]; ring⟩
    omega
  have hl0 : (l : K) ≠ 0 := natCast_ne_zero' l hpr.ne_zero
  have hu0 : (u : K) ≠ 0 := by
    intro h
    have := norm_intCast_eq_one (K := K) l hu'
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set t : K := (l : K) ^ (m - v) * (u : K)⁻¹ with ht
  obtain ⟨t', ht'⟩ := (IsUnitBall.mem_range_iff (O := O) t).2 (by
    rw [ht, norm_mul, norm_pow, norm_inv, norm_intCast_eq_one l hu', inv_one, mul_one, norm_l l]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hpr.one_le)))
  refine ⟨t', ?_⟩
  rw [ht', ht, hu]
  push_cast
  rw [mul_comm ((l : K) ^ v), ← mul_assoc, mul_assoc _ _ (u : K), inv_mul_cancel₀ hu0,
    mul_one, ← pow_add, Nat.sub_add_cancel hm]

theorem exists_mem_Y'_Lc_cls_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → H + η < l → 10 * H + 2 ≤ l → ∀ c : ℕ, ∀ w ∈ D.Zl, (l : K) ^ c • D.Lc w ∈ D.Z → ∃ y ∈ D.Y', D.Lc (D.cls y) = (l : K) ^ (c + η + (N + 1) * η) • D.Lc w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hJ hU hN hηH hl h10 c w hw hc
  obtain ⟨-, hVal, hInt⟩ := GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation O K l e a ι η H D U N hJ hU hN hηH
  obtain ⟨-, hR0, hv, hcard, hcard'⟩ := hVal hl

  obtain ⟨z, hz, hRz⟩ := hInt h10 (c : ℤ) (D.LcZ ⟨w, hw⟩) ⟨_, rfl⟩ (by
    rw [zpow_natCast, D.coe_LcZ]; exact hc)
  rw [zpow_natCast] at hz
  have hRz' : (((polyR l e U η).eval 0 : ℤ) : K) • D.Lc w = D.Lc z := by
    simpa using congrArg Subtype.val hRz

  obtain ⟨t, ht⟩ := exists_mul_intCast_eq (O := O) (K := K) l hR0 (m := (N + 1) * η)
    (by omega)
  have hx1 : t • ((l : K) ^ c • (z : D.Pol)) ∈ D.Z := D.Z.smul_mem t hz
  have hLx1 : D.Lc (t • ((l : K) ^ c • (z : D.Pol))) = (l : K) ^ (c + (N + 1) * η) • D.Lc w := by
    rw [← algebraMap_smul K t, map_smul, map_smul, ← hRz', smul_smul, smul_smul, pow_add]
    congr 1
    rw [← ht]; ring

  obtain ⟨z'', hz'', hv''⟩ := (GlobalTheory.T.prime_pow_divisibility_of_descentDatum O K l e a ι η H D).1 _ hx1

  have hz3 : z'' ∈ (D.desc.Y η).map (D.cls.restrictScalars O) := by
    rw [Descent.map_Y]; exact hz''
  obtain ⟨y'', hy'', rfl⟩ := hz3
  refine ⟨(X : K⟦X⟧) ^ e • y'', (Descent.mem_Y' _).2 ⟨y'', hy'', rfl⟩, ?_⟩
  have h1 : D.cls ((X : K⟦X⟧) ^ e • y'') = (l : K) ^ η • (t • ((l : K) ^ c • (z : D.Pol))) := by
    rw [hv'']; rfl
  rw [h1, map_smul, hLx1, smul_smul, ← pow_add]
  congr 2
  ring

end GlobalTheory.LcImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatricesStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  first | exact @GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat | exact GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat | (intros; apply GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeEqMulPrimitiveRootSubOnePow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_pow_n0_mul (l : ℕ) [hl : Fact l.Prime] (H : ℕ) : H ≤ l ^ (n0 l H) * (l - 1) := by
  unfold n0
  apply Nat.sInf_mem (s := {n | H ≤ l ^ n * (l - 1)})
  have h2 : 2 ≤ l := hl.out.two_le
  refine ⟨H, ?_⟩
  show H ≤ l ^ H * (l - 1)
  calc H ≤ l ^ H := (Nat.lt_pow_self (by omega : 1 < l)).le
    _ ≤ l ^ H * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem exists_prime_eq_mul_primitiveRoot_sub_one_pow (l : ℕ) [hl : Fact l.Prime] (H : ℕ)
    (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ (1 + n0 l H))) :
    ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hH : (H : ℝ) ≤ (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have h := le_pow_n0_mul l H
    have h1 : 1 ≤ l := hl.out.one_lt.le
    calc (H : ℝ) ≤ ((l ^ n0 l H * (l - 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by push_cast [Nat.cast_sub h1]; ring
  have hDpos : 0 < (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    positivity
  have hnorm := norm_primitiveRoot_sub_one l (1 + n0 l H) (by omega) ζ hζ
  rw [Nat.add_sub_cancel_left] at hnorm
  have hpos : 0 < ‖ζ - 1‖ := by rw [hnorm]; positivity
  have hne : ζ - 1 ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨(l : PadicComplex l) / (ζ - 1) ^ H, ?_, (div_mul_cancel₀ _ (pow_ne_zero H hne)).symm⟩
  rw [norm_div, norm_pow, norm_natCast_prime_padicComplex, div_le_one (pow_pos hpos H), hnorm,
    ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul, div_le_one hDpos]
  exact hH

end GlobalTheory.Cyc.Decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeNormCyclotomicCharNeOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormChar

theorem split_trivial (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M,
      x ^ Ideal.absNorm v.asIdeal - x ∈ P) : Module.finrank K M = 1 := by
  by_contra h1
  have h2 : 1 < Module.finrank K M := by have := Module.finrank_pos (R := K) (M := M); omega
  obtain ⟨T, hT, hc⟩ := GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius K M
  refine GlobalTheory.T.not_forall_exists_two_degree_one_primes_over K M (S ∪ T) (hS.union hT) fun v hv => ?_
  simp only [Set.mem_union, not_or] at hv
  obtain ⟨hn, hN⟩ := hc v hv.2 (h v hv.1)
  rw [← hn] at h2
  have := v.isMaximal
  obtain ⟨P, P', hP, hP', hne⟩ := (Set.one_lt_ncard_iff (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M))).1 h2
  have := hP.2
  have := hP'.2
  exact ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ⟨P', hP'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P'⟩,
    fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hP.2, hP'.2, hN P hP, hN P' hP'⟩

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in

theorem _root_.GlobalTheory.NormChar.smulComm (K L : Type) [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := by
  refine ⟨fun σ a x => ?_⟩
  apply RingOfIntegers.ext
  have h1 : ((a • x : 𝓞 L) : L) = algebraMap K L a * x := by
    rw [Algebra.smul_def]; rfl
  have h3 : ((σ • (a • x) : 𝓞 L) : L) = σ ((a • x : 𝓞 L) : L) := rfl
  rw [h3, h1, Algebra.smul_def]
  push_cast
  rw [map_mul, AlgEquiv.commutes]
  rfl

attribute [local instance] smulComm

theorem eq_top_of_frob (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
      ∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ Q → σ ∈ H) : H = ⊤ := by
  set M := IntermediateField.fixedField H with hM
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have h1 : Module.finrank K M = 1 := by
    refine split_trivial K M S hS fun v hv P hP x => ?_
    have := hP.1
    have := hP.2
    obtain ⟨Q, hQ, hQ'⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 L)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) Q
    have hH := h v hv Q hQ hQv σ hσ
    have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
      rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h6 := hσ (algebraMap (𝓞 M) (𝓞 L) x)
    rw [h5] at h6
    have h7 : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ) (algebraMap (𝓞 M) (𝓞 L) x) = algebraMap (𝓞 M) (𝓞 L) x := by
      apply RingOfIntegers.ext
      exact (x : M).2 ⟨σ, hH⟩
    rw [h7] at h6
    rw [hQ'.over, Ideal.mem_comap, map_sub, map_pow, ← neg_mem_iff, neg_sub]
    exact h6
  have h2 : M = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  rw [← IntermediateField.fixingSubgroup_fixedField H, ← hM, h2, IntermediateField.fixingSubgroup_bot]

theorem exists_prime_norm_char_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  intro K _ _ m hm hirr χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero m := ⟨hm.ne_zero⟩
  let L := CyclotomicField m K
  have : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  let e := IsCyclotomicExtension.autEquivPow L hirr
  have hz := IsCyclotomicExtension.zeta_spec m K L
  have hm0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hH := eq_top_of_frob K L (χ.comp e.toMonoidHom).ker {v | v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}}
    (Ideal.finite_factors hm0) (fun v hv Q hQ hQv σ hσ => by
      have hζ := hz.toInteger_isPrimitiveRoot
      have hmQ : (m : 𝓞 L) ∉ Q := by
        intro hmQ
        apply hv
        rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton, hQv.over, Ideal.mem_comap, map_natCast]
        exact hmQ
      have h3 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hζ.pow_eq_one hmQ
      have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
        rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h5] at h3
      have h4 : σ (IsCyclotomicExtension.zeta m K L) =
          IsCyclotomicExtension.zeta m K L ^ Ideal.absNorm v.asIdeal := by
        have := congrArg (fun y : 𝓞 L => (y : L)) h3
        exact this
      have h6 := hz.autToPow_spec K σ
      rw [h4] at h6
      have h7 : ((hz.autToPow K σ : (ZMod m)ˣ) : ZMod m).val ≡ Ideal.absNorm v.asIdeal [MOD m] := by
        have := (hz.isOfFinOrder hm.ne_zero).pow_eq_pow_iff_modEq.1 h6
        rwa [← hz.eq_orderOf] at this
      refine hcon v (e σ) ?_
      rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h7, ZMod.natCast_zmod_val]
      rfl)
  apply hχ
  ext1 u
  have : e.symm u ∈ (χ.comp e.toMonoidHom).ker := hH ▸ Subgroup.mem_top _
  simpa using this

end GlobalTheory.NormChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLat
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_Ainf_series_limit (l : ℕ) [Fact l.Prime] (a : ℕ → Ainf l) :
    ∃ x : Ainf l, ∀ n : ℕ, ∃ y : Ainf l,
      x - ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i = ((l : ℕ) : Ainf l) ^ n * y := by
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : Ainf l)}) (Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  have key : ∀ (n : ℕ) (u v : Ainf l),
      u ≡ v [SMOD ((Ideal.span {((l : ℕ) : Ainf l)}) ^ n • ⊤ : Submodule (Ainf l) (Ainf l))] ↔
        ((l : ℕ) : Ainf l) ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨x, hx⟩ := hc.toIsPrecomplete.prec
    (f := fun n => ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      exact Finset.dvd_sum fun i hi =>
        Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.mp hi).1) _)
  refine ⟨x, fun n => ?_⟩
  have := hx n
  rw [key, ← dvd_neg, neg_sub] at this
  exact this

theorem exists_series_limit_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ)
    (c : ℕ → P.R.BdR) (h0 : ∀ k, c k ∈ FilB P 0)
    (hc : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) :
    ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀,
      b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  choose k hk using hc
  let K : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (n + 1), k i
  have hK1 : ∀ n, k n ≤ K n := fun n => by
    simp only [K, Finset.sum_range_succ]
    omega
  have hK2 : ∀ n, K n ≤ K (n + 1) := fun n => by
    simp only [K, Finset.sum_range_succ k (n + 1)]
    omega
  have hblock : ∀ n R, K n ≤ R →
      ∑ j ∈ Finset.range R, c j - ∑ j ∈ Finset.range (K n), c j ∈ Lat AI M n := by
    intro n R hR
    rw [← Finset.sum_Ico_eq_sub _ hR]
    exact AddSubgroup.sum_mem _ fun j hj => hk n j ((hK1 n).trans (Finset.mem_Ico.mp hj).1)
  choose a ha using fun n => (mem_Lat AI).mp (hblock n (K (n + 1)) (hK2 n))
  have htel : ∀ n, ∑ j ∈ Finset.range (K n), c j - ∑ j ∈ Finset.range (K 0), c j -
      io AI (∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (ha n)
      rw [Finset.sum_range_succ (fun i => ((l : ℕ) : Ainf l) ^ i * a i), map_add]
      convert this using 1
      ring
  obtain ⟨x, hx⟩ := exists_Ainf_series_limit l a
  refine ⟨∑ j ∈ Finset.range (K 0), c j + io AI x,
    add_mem (Submodule.sum_mem _ fun j _ => h0 j) (io_mem AI x), fun n => ⟨K n, fun R hR => ?_⟩⟩
  obtain ⟨y, hy⟩ := hx n
  have h1 := io_mem_Lat AI M n y
  rw [← hy, map_sub] at h1
  have := sub_mem (sub_mem h1 (FilB_le_Lat AI (n := n) (htel n))) (hblock n R hR)
  convert this using 1
  ring

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepWeilJumpsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_rep_weil_jumps : ∀ D : D7, SumRepresentations.tie0 D → ∀ (i : D.nd.Loc) (a : ℕ) (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i))) (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (p q : ∀ w, D.naut.LP w) (m : (D.host.E →+* ℂ) → Multiset ℂ) (c : (D.host.E →+* ℂ) → ℂ), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = p w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = m ((D.naut.iotaQC i).toRingHom.comp τ)) → (SumRepresentations.At.ContQ D.nd i χ ∧ IsSSRep χ ∧ (∀ w, D.naut.wdOf i χ w = q w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i χ τ).map (fun n : ℤ => (n : ℂ)) = {c ((D.naut.iotaQC i).toRingHom.comp τ)}) → ∃ ρ' : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ' ∧ IsSSRep ρ' ∧ (∀ w, D.naut.wdOf i ρ' w = D.naut.lpChar (p w) (q w)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ' w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ' τ).map (fun n : ℤ => (n : ℂ)) = (m ((D.naut.iotaQC i).toRingHom.comp τ)).map (· + c ((D.naut.iotaQC i).toRingHom.comp τ))) := by
  first | exact @GlobalTheory.twist_compatible | exact GlobalTheory.twist_compatible | (intros; apply GlobalTheory.twist_compatible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem goodO_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (good_integers l LL).1

end GlobalTheory.LocalIntegers
end

