import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0299
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0011
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0011
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0292
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0295
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0296
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0297
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftVeryAmpleSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem inv_of_mul_eq {A : Type} [CommRing A] {a a' b b' g g' : A} (h : a = g * b) (ha : a * a' = 1)
    (hb : b * b' = 1) (hg : g * g' = 1) : a' = g' * b' := by
  linear_combination (-(g' * b' * a')) * h + (g' * b') * ha + (-a') * hb + (-(a' * b * b')) * hg

variable {X X' : Scheme.{0}}

theorem exists_inv_of_isUnit_coord {N : LB X} {a : ℤ} {V : X.Opens} (x : SecOn (pw N a) V)
    (hx : ∀ k : N.ι, IsUnit (GlobalTheory.LB.coord x k)) :
    ∃ y : SecOn (pw N (-a)) V, secMulOn rfl x y = oneOn N (add_neg_cancel a) V := by
  have hy : (fun k : N.ι => (((hx k).unit⁻¹ : Γ(X, V ⊓ N.U k)ˣ) : Γ(X, V ⊓ N.U k))) ∈
      Geo.Tor.secOn (pw N (-a)) V := by
    intro i j
    have h := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    refine inv_of_mul_eq h ?_ ?_ ?_
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx i))).trans (map_one _))
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx j))).trans (map_one _))
    · refine (map_mul _ _ _).symm.trans ?_
      have e : ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ (-a) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) = 1 := by
        rw [← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one]
      exact (congrArg _ e).trans (map_one _)
  refine ⟨GlobalTheory.LB.mkSec _ hy, GlobalTheory.LB.sec_ext fun k => ?_⟩
  exact IsUnit.mul_val_inv (hx k)

theorem isUnit_coord_of_congr (π : X' ⟶ X) (hπ : Function.Surjective π) {M : LB X} {L : LB X'}
    (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L (M.pull π)) (hw : w.IsGen) {V : X.Opens}
    {V' : X'.Opens} (e : π ⁻¹ᵁ V = V') (x : SecOn M V) (t : SecOn L V')
    (h : SecOn.congr hL (LB.isLB_pull hM π) w hw V' t = SecOn.pullLE M π V V' e.ge x)
    (ht : ∀ q, IsUnit (GlobalTheory.LB.coord t q)) (k : M.ι) : IsUnit (GlobalTheory.LB.coord x k) := by
  have hb : V ⊓ M.U k ≤ X.basicOpen (GlobalTheory.LB.coord x k) := by
    intro z hz
    obtain ⟨z', rfl⟩ := hπ z
    let j : (M.pull π).ι := fun _ => k
    have hz₁ : z' ∈ V' := e.le hz.1
    have hz₂ : z' ∈ (M.pull π).U j := by rw [pull_U]; exact hz.2
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hL.cover.ge (TopologicalSpace.Opens.mem_top z'))
    let O : X'.Opens := V' ⊓ (M.pull π).U j ⊓ L.U q
    have hp : O ≤ V' ⊓ (M.pull π).U j := inf_le_left
    have hq' : O ≤ V' ⊓ L.U q := inf_le_inf_right _ inf_le_left
    have hpq : O ≤ (M.pull π).U j ⊓ L.U q := inf_le_inf_right _ inf_le_right
    have c := SecOn.coord_congr hL (LB.isLB_pull hM π) w hw t j q hp hq' hpq
    rw [h] at c
    have hu : IsUnit (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [c]
      exact (Units.isUnit _).map (rs X' hpq) |>.mul ((ht q).map (rs X' hq'))
    have hz' : z' ∈ X'.basicOpen (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [X'.basicOpen_of_isUnit hu]
      exact ⟨⟨hz₁, hz₂⟩, hq⟩
    erw [Scheme.basicOpen_res] at hz'
    have hz'' := hz'.2
    rw [SecOn.coord_pullLE, Scheme.basicOpen_appLE] at hz''
    exact hz''.2
  have hu : IsUnit (rs X (X.basicOpen_le _) (GlobalTheory.LB.coord x k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (GlobalTheory.LB.coord x k)
  simpa only [rs_rs, rs_self] using hu.map (rs X hb)

variable {R : Type} [CommRing R] (I : Ideal R)

theorem ker_factor_le_nilradical (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    RingHom.ker (Ideal.Quotient.factor h) ≤ nilradical (R ⧸ I ^ (e + 1 + 1)) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hy2 : y ^ 2 ∈ I ^ (e + 1) * I ^ (e + 1) := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hx
  rw [← pow_add] at hy2
  exact Ideal.pow_le_pow_right (by omega) hy2

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  delta ReciprocityTheory.ChartRestriction.G.Out.thickTrans
  have key : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), Function.Surjective φ →
      RingHom.ker φ ≤ nilradical A → Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    intro A B _ _ φ hφ hker
    constructor
    intro p
    haveI := p.isPrime
    have hk : RingHom.ker φ ≤ p.asIdeal := le_trans hker (nilradical_le_prime p.asIdeal)
    refine ⟨⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩, ?_⟩
    show PrimeSpectrum.comap φ ⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩ = p
    ext1
    show Ideal.comap φ (Ideal.map φ p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hk]
  exact key _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_le_nilradical I e _)

variable (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))

include hβ in

theorem surjective_tower (e : ℕ) : Function.Surjective (β e) := by
  exact (MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans I e)).surj

theorem isUnit_coord_of_redL (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) {V : (Y (e + 1)).left.Opens}
    {V' : (Y e).left.Opens} (h : β e ⁻¹ᵁ V = V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (ht : ∀ q, IsUnit (SecOnR.coord (redL I Y β hβ L w hL e V V' h.ge x) q)) (k : (L (e + 1)).ι) :
    IsUnit (SecOnR.coord x k) :=
  isUnit_coord_of_congr (β e) (surjective_tower I Y β hβ e) (hL e).1 (hL (e + 1)).1 (w e) (hL e).2 h
    x (redL I Y β hβ L w hL e V V' h.ge x)
    ((SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
      (hL e).2 V')).apply_symm_apply _) ht k

theorem exists_lifts_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hge : ∀ e (S : Finset (Fin (m + 1))), D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have hsurj : ∀ e (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red I Y N D β hβ v hN hge (d : ℤ) e S) := fun e S hS =>
    (redL_surjective_ker R I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)).1
  have hl : ∀ e (S : Finset (Fin (m + 1))) (t : SecOn (pw (N e) (d : ℤ)) (D e S)),
      ∃ x : SecOn (pw (N (e + 1)) (d : ℤ)) (D (e + 1) S), S.Nonempty →
        red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ x) = SecOnR.of _ _ _ t := by
    intro e S t
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hsurj e S hS (SecOnR.of _ _ _ t)
      exact ⟨(SecOnR.of _ _ _).symm x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose lf hlf using hl
  let sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S) :=
    fun e j S => Nat.rec (motive := fun e => SecOn (pw (N e) (d : ℤ)) (D e S))
      (GlobalTheory.LB.ofSec (s j) (D 0 S)) (fun e t => lf e S t) e
  refine ⟨sh, fun j S _ => rfl, fun e j S hS => hlf e S _ hS, fun e i S hi =>
    exists_inv_of_isUnit_coord _ ?_⟩
  induction e with
  | zero =>
    intro k
    have hle : D 0 S ≤ nonzeroLocus (s i) := by
      rw [hD0]
      exact iInf₂_le i hi
    exact SecOn.isUnit_rs_of_le_nonzeroLocus (s i) k (inf_le_right : D 0 S ⊓ (N 0).U k ≤ (N 0).U k)
      (inf_le_left.trans hle)
  | succ e ih =>
    intro k
    refine isUnit_coord_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
      (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (hDβ e S)
      (SecOnR.of _ _ _ (sh (e + 1) i S)) (fun q => ?_) k
    have hr : red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) i S)) =
        SecOnR.of _ _ _ (sh e i S) := hlf e S (sh e i S) ⟨i, hi⟩
    change IsUnit (SecOnR.coord (red I Y N D β hβ v hN hge (d : ℤ) e S
      (SecOnR.of _ _ _ (sh (e + 1) i S))) q)
    rw [hr]
    exact ih q

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsOpIntegralRankOne
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.HsPsProof

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

section General

variable {K V : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

theorem hsOp_integral_rank_one (m : Measure K) [IsFiniteMeasure m] {u : K → V} (hu : Continuous u)
    {φ : K → ℝ} (hφ : Continuous φ) {P : K → V →L[ℂ] V} (hPc : Continuous P)
    (hP : ∀ k b, P k b = ⟪u k, b⟫_ℂ • u k) (d : ℝ) :
    hsOp ((d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m) =
      d ^ 2 * ∫ p, φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 ∂(m.prod m) := by
  have hφC : Continuous fun k => ((φ k : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ
  have hInt : Integrable (fun k => ((φ k : ℝ) : ℂ) • P k) m :=
    (integrableOn_univ).mp ((hφC.smul hPc).continuousOn.integrableOn_compact isCompact_univ)
  set A : V →L[ℂ] V := (d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m with hA
  have hkey : ∀ y x : V, ⟪y, A x⟫_ℂ =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, x⟫_ℂ * ⟪y, u k⟫_ℂ) ∂m := by
    intro y x
    have hIx : Integrable (fun k => (((φ k : ℝ) : ℂ) • P k) x) m :=
      (ContinuousLinearMap.apply ℂ V x).integrable_comp hInt
    rw [hA, _root_.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hInt,
      ← integral_inner hIx]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_root_.smul_apply, inner_smul_right, hP]
  have hQ : ∀ v : V, ⟪v, A v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [hkey]
    have : ∀ k, ((φ k : ℝ) : ℂ) * (⟪u k, v⟫_ℂ * ⟪v, u k⟫_ℂ) =
        ((φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [← inner_conj_symm (u k) v, Complex.conj_mul']
      push_cast; ring
    simp_rw [this]
    rw [integral_complex_ofReal]
    push_cast; ring
  have hQ' : ∀ v : V, ⟪A v, v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [← inner_conj_symm, hQ, Complex.conj_ofReal]
  set b := stdOrthonormalBasis ℂ V with hb
  have hsum : ∀ v : V, ∑ i, ⟪v, b i⟫_ℂ * ⟪A (b i), v⟫_ℂ = ⟪A v, v⟫_ℂ := by
    intro v
    simp_rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [b.sum_inner_mul_inner]
  have hterm : ∀ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
    intro i
    rw [← hkey, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have hintg : ∀ i ∈ (Finset.univ : Finset _), Integrable
      (fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ)) m := by
    intro i _
    have hc : Continuous fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) :=
      hφC.mul ((hu.inner continuous_const).mul (continuous_const.inner hu))
    exact (integrableOn_univ).mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hC : ((hsOp A : ℝ) : ℂ) =
      ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
    calc ((hsOp A : ℝ) : ℂ) = ∑ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) := by
          simp only [hsOp, hb]; push_cast; rfl
      _ = ∑ i, (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m :=
          sum_congr rfl fun i _ => hterm i
      _ = (d : ℂ) * ∫ k, ∑ i, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
          rw [← mul_sum, integral_finset_sum _ hintg]
      _ = (d : ℂ) * ∫ k, ((φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) : ℝ) : ℂ) ∂m := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only []
          rw [← mul_sum, hsum, hQ']
          push_cast; rfl
      _ = ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]
          push_cast; rfl
  have hR : hsOp A = d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m := by
    exact_mod_cast hC
  have hF : Continuous fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 :=
    ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd)).mul
      (((hu.comp continuous_fst).inner (hu.comp continuous_snd)).norm.pow 2)
  have hFi : Integrable (fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2) (m.prod m) :=
    (integrableOn_univ).mp (hF.continuousOn.integrableOn_compact isCompact_univ)
  rw [hR, integral_prod _ hFi]
  have e1 : ∀ k, ∫ k', φ k * φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m =
      φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m := by
    intro k
    rw [← integral_const_mul]
    simp only [mul_assoc]
  have e2 : ∀ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) =
      d * (φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) := fun k => by ring
  simp_rw [e1, e2]
  rw [integral_const_mul]
  ring

end General

variable {n : ℕ} {ε : Fin n → Bool}

private lemma posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

private lemma cont_phiK (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (phiK μ x : KG ε → ℝ) := by
  have hm : Continuous (fun k : KG ε => toMK k) :=
    (continuous_toM ε).comp continuous_subtype_val
  have hz : Continuous (fun k : KG ε => toMK k⁻¹ * x * toMK k) :=
    ((hm.comp continuous_inv).mul continuous_const).mul hm
  refine Complex.continuous_re.comp ?_
  exact (phiM_differentiableOn μ).continuousOn.comp_continuous hz
    (fun k => posSet_subset_omega (posDef_conj k hx))

private lemma cK_mul {Λ : Fin n → ℝ} (T : KType ε Λ) (a b : KG ε) :
    cK T (a⁻¹ * b) = ‖⟪T.op a T.w, T.op b T.w⟫_ℂ‖ := by
  rw [cK, CompactHaarProbability.op_mul, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem hsPs : HsPs := by
  intro n ε Λ T μ x hx
  have hφc : Continuous (phiK μ x : KG ε → ℝ) := cont_phiK μ hx
  have hφeq : ∀ k : KG ε, PhiM μ (toMK k⁻¹ * x * toMK k) = ((phiK μ x k : ℝ) : ℂ) := fun k =>
    Complex.ext (by simp [phiK]) (by simp [(phiM_posDef μ (posDef_conj k hx)).2])
  have hps : psM T μ x = ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((phiK μ x k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) := by
    unfold psM dk
    simp_rw [hφeq]
    rw [integral_smul_measure, ENNReal.toReal_inv, ← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hu : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have hPc : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    ((KType_continuous_op T).mul continuous_const).mul ((KType_continuous_op T).comp continuous_inv)
  rw [hps, hsOp_integral_rank_one (dk ε) hu hφc hPc (conj_projection_apply T)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hI, cK_mul]

end GlobalTheory.CompanionTheory.HsPsProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevel
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_fiber {R I J : Type} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (π : I → J) {e : I → R} (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (fun c : J => ∑ c' with π c' = c, e c') := by
  classical
  have hmul : ∀ c d : J, (∑ c' with π c' = c, e c') * (∑ c' with π c' = d, e c') =
      if c = d then ∑ c' with π c' = c, e c' else 0 := by
    intro c d
    rw [Finset.sum_mul_sum]
    split_ifs with hcd
    · subst hcd
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · exact he.idem i
      · intro j _ hji
        exact he.ortho hji.symm
      · intro h; exact absurd hi h
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_
      rintro rfl
      exact hcd ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  refine ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩
  · change _ * _ = _
    rw [hmul, if_pos rfl]
  · change _ * _ = _
    rw [hmul, if_neg hcd]
  · rw [Finset.sum_fiberwise]
    exact he.complete

theorem chain_pow {M : Type} [Monoid M] {p : ℕ} {x : ℕ → M} (h : ∀ k, x (k + 1) ^ p = x k)
    (m d : ℕ) : x (m + d) ^ p ^ d = x m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem mul_sub_pow {S : Type} [CommRing S] {a x y : S} (h : a * (x - y) = 0) (q : ℕ) :
    a * (x ^ q - y ^ q) = 0 := by
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x y q
  rw [hd, ← mul_assoc, h, zero_mul]

theorem val_modEq {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (c : ZMod N) :
    c.val ≡ (ZMod.castHom h (ZMod M) c).val [MOD M] := by
  have h0 := map_natCast (ZMod.castHom h (ZMod M)) c.val
  rw [ZMod.natCast_zmod_val] at h0
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact h0.symm

variable {l : ℕ} [Fact l.Prime]

theorem sharp_xi_pow (ε : Eps l) (t : PAlg l) (m d : ℕ) :
    t.sharp (t.s (ε.e (m + d))) ^ l ^ d = t.sharp (t.s (ε.e m)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, chain_pow ε.succ]

theorem sharp_xi_period (ε : Eps l) (t : PAlg l) (m : ℕ) :
    t.sharp (t.s (ε.e m)) ^ l ^ m = 1 := by
  have := sharp_xi_pow ε t 0 m
  rw [zero_add] at this
  rw [this]
  exact ε.sharp_e t

theorem coi_descend (ε : Eps l) (t : PAlg l) (r : ℕ → t.A) (hr : ∀ m, r (m + 1) ^ l = r m)
    {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A) (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) :
    CompleteOrthogonalIdempotents
        (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
      ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') *
        (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨coi_fiber _ he, fun c => ?_⟩
  rw [(sharp_sum t _ e (fun i _ => he.idem i) (fun i _ j _ hij => he.ortho hij)).1, Finset.sum_mul]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hπ := (Finset.mem_filter.1 hc').2
  have h1 := mul_sub_pow (hc c') (l ^ d)
  rw [← map_pow, chain_pow hr, ← pow_mul, mul_comm c'.val, pow_mul, sharp_xi_pow] at h1
  have h2 : t.sharp (t.s (ε.e m)) ^ c'.val = t.sharp (t.s (ε.e m)) ^ c.val := by
    have hv := val_modEq (pow_dvd_pow l h) c'
    rw [hπ] at hv
    rw [pow_eq_pow_mod c'.val (sharp_xi_period ε t m), pow_eq_pow_mod c.val (sharp_xi_period ε t m)]
    exact congrArg _ hv
  rwa [h2] at h1

end GlobalTheory.CompanionTheory.ContUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InclRedM
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedPull

theorem incl_redM : ∀ {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) (j : ℕ) (z : HO Q j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r c)).pull j (redM Q r c j z) =
      redM Q' r c j ((incl h).o.pull j z) := by
  intro b L Q Q' h r c j z
  exact sq_toSq (incl h) _ _ (fun _ _ _ => trivial) (incl_std h r c) j z

end GlobalTheory.CompanionTheory.RedPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquivStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_brauer_roots_unity_equiv : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | exact GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | (intros; apply GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTatePeriodNotFilteredStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_period_not_filtered : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exact_degrees_of_product | exact GlobalTheory.CompanionTheory.LTPer.exact_degrees_of_product | (intros; apply GlobalTheory.CompanionTheory.LTPer.exact_degrees_of_product <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsFormStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_vanishing_ideal_iff_kills_form : ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n), f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  first | exact @GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm | exact GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm | (intros; apply GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlanePropOfAllStrongApproxStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_prop_of_all_strong_approx : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → HermitianPlaneStrongApprox σ β) → Sa2.PropPlane := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx | exact GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransferStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_transfer : KH.PolyTf := by
  first | exact @GlobalTheory.CompanionTheory.PolyTfCon.polyTf | exact GlobalTheory.CompanionTheory.PolyTfCon.polyTf | (intros; apply GlobalTheory.CompanionTheory.PolyTfCon.polyTf <;> assumption)
end

