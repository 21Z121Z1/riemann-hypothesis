import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

set_option maxHeartbeats 1000000 in

theorem lt_period_conj_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  intro l _ P AI T s hs x hx hφ h1 h2 hj g
  obtain ⟨-, -, hsh, hinv, -, -, -, htz, tadd, t0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have iter_mul : ∀ (m : ℕ) (a b : P.R.B), P.φB^[m] (a * b) = P.φB^[m] a * P.φB^[m] b := by
    intro m a b
    induction m generalizing a b with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_mul]
  have iter_one : ∀ m : ℕ, P.φB^[m] (1 : P.R.B) = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]
  have iter_act : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
    intro m b
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]
  have ev_mul : ∀ (m : ℕ) (a b : P.R.B), ev P m (a * b) = ev P m a * ev P m b := by
    intro m a b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply]
  obtain ⟨w, hw⟩ : ∃ w : P.R.B, x * w = 1 := ⟨_, hx.mul_val_inv⟩
  set y := P.actQ g x * w with hy
  have hyx : y * x = P.actQ g x := by rw [hy, mul_assoc, mul_comm w x, hw, mul_one]

  have hfix : P.φB^[s] y = y := by
    have e1 : P.φB^[s] x * P.φB^[s] w = 1 := by rw [← iter_mul, hw, iter_one]
    rw [hφ] at e1
    rw [hy, iter_mul, iter_act, hφ, map_mul, map_natCast]
    calc (l : P.R.B) * P.actQ g x * P.φB^[s] w = P.actQ g x * (((l : P.R.B) * x * P.φB^[s] w) * w) := by
          linear_combination (-(l : P.R.B) * P.actQ g x * P.φB^[s] w) * hw
      _ = P.actQ g x * w := by rw [e1, one_mul]

  have key : ∀ (k : ℤ) (e u v z : P.R.BdR), e = tz P k * u → u * v = 1 → u ∈ Fil P 0 → v ∈ Fil P 0 →
      z * e = P.actQdR g e → z ∈ Fil P 0 := by
    intro k e u v z he huv hu hv hz
    have hk : tz P k * tz P (-k) = 1 := by rw [← tadd, add_neg_cancel, t0]
    have hz' : z * e = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * tz P k * P.actQdR g u := by
      rw [hz, he, map_mul, htz]
    have hzz : z = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v := by
      linear_combination (-z + algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v) * hk
        - z * tz P k * tz P (-k) * huv - tz P (-k) * v * z * he + tz P (-k) * v * hz'
    rw [hzz]
    exact Fil_mul_right (Fil_mul_left (q_mem_Fil P _) (Fil_act g hu)) hv
  have hev : ∀ j, ev P j y * ev P j x = P.actQdR g (ev P j x) := by
    intro j
    rw [← ev_mul, hyx, ev_act]
  have hfil : ∀ j < s, ev P j y ∈ Fil P 0 := by
    intro j hjs
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
        have := (hsh 1 (-1) (P.ιB x)).1 h1
        rwa [show (1 : ℤ) + -1 = 0 by norm_num] at this
      have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
        intro h
        apply h2
        exact (hsh 2 (-1) (P.ιB x)).2 (by rw [show (2 : ℤ) + -1 = 1 by norm_num]; exact h)
      obtain ⟨v, hv, huv⟩ := hinv _ hu0 hu1
      refine key 1 (ev P 0 x) _ v _ ?_ huv hu0 hv (hev 0)
      change P.ιB x = tz P 1 * (tz P (-1) * P.ιB x)
      rw [← mul_assoc, ← tadd, show (1 : ℤ) + -1 = 0 by norm_num, t0, one_mul]
    · obtain ⟨e0, e1⟩ := hj j hpos hjs
      obtain ⟨v, hv, huv⟩ := hinv _ e0 e1
      exact key 0 (ev P j x) (ev P j x) v _ (by rw [t0, one_mul]) huv e0 hv (hev j)
  obtain ⟨a, ha, hya⟩ := GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T s hs y hfix hfil
  exact ⟨a, ha, by rw [← hyx, hya]⟩

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FrobDenom

section Abstract

variable {O RA RW M : Type} [CommRing O] [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  [AddCommGroup M] [Module O M]

theorem repr_incl {κ : Type} (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW) (u : RA ⊗[O] M) (k : κ) :
    (Algebra.TensorProduct.basis RW tb).repr
        (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M) u) k =
      incl ((Algebra.TensorProduct.basis RA tb).repr u k) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]

theorem map_smul_left (f : RW →ₐ[O] RW) (r : RW) (z : RW ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (r • z) =
      f r • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]

theorem mem_range_of_frob {κ : Type} [Fintype κ] (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (r : RA) (z w : RW ⊗[O] M)
    (hw : w ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)))
    (h : TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) z = incl r • z + w) :
    z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  classical
  obtain ⟨w', rfl⟩ := hw
  set tt := Algebra.TensorProduct.basis RW tb with htt
  set ta := Algebra.TensorProduct.basis RA tb with hta
  have key := hA κ Unit (Matrix.of fun k _ => tt.repr z k) (Matrix.diagonal fun _ => r) 1
    (Matrix.of fun k _ => ta.repr w' k) (by
      ext k u
      have h1 := congrArg (fun x => tt.repr x k) h
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      rw [htt, GlobalTheory.Sandwich.repr_phi, repr_incl, ← htt, ← hta] at h1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_map (map_zero _)]
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
      exact h1)
  choose c hc using fun k => key k ()
  refine ⟨∑ k, c k ⊗ₜ[O] tb k, ?_⟩
  conv_rhs => rw [← tt.sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hc k
  simp only [Matrix.of_apply] at this
  rw [← this, htt, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  simp

end Abstract

section Alg

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

theorem φ_prod (φ : A →ₐ[O] A) (X Q : A) (hXQ : φ X = X * Q) (m : ℕ) :
    φ (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) =
      (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) * ∏ j ∈ Finset.range (m + 1), (φ ^ j) Q := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hXQ, map_mul]

theorem multiset_dvd (f : ℕ → A) (m : ℕ) (J : Multiset ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    (J.map f).prod ∣ (∏ j ∈ Finset.range (m + 1), f j) ^ Multiset.card J := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons j J ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    refine mul_dvd_mul (ih fun i hi => hJ i (Multiset.mem_cons_of_mem hi)) ?_
    exact Finset.dvd_prod_of_mem f
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hJ j (Multiset.mem_cons_self j J))))

theorem X_dvd (φ : A →ₐ[O] A) (X : A) (m : ℕ) : X ∣ ∏ j ∈ Finset.range (m + 1), (φ ^ j) X := by
  have := Finset.dvd_prod_of_mem (fun j => (φ ^ j) X) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa using this

end Alg

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem jD_smulA (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (x : W.DD T) : E.jD T (a • x) = inclR (E.io a) • E.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext]

set_option maxHeartbeats 1000000 in

theorem of_sand (E : EtTie W RA RW inclR φR gR πA)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = S.map inclR * Z * S'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (T : LocLat G Qp LL O) {κ : Type} [Fintype κ] (tb : Module.Basis κ O ↥T.L.T) (m₀ : ℕ)
    (hm₀ : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
      TensorProduct.map (LinearMap.mulLeft O (inclR (E.io W.X) ^ m₀)) LinearMap.id (E.jD T x))
    (J : Multiset ℕ) (y : W.DD T) (hy : (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T)
    (b : TW RW T) (hb : TWmap φR T b - b = E.jD T y) (m : ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft O
      (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
        TAinf inclR T := by
  set Y := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X with hY
  set L := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.Q with hL
  set Jp := (J.map fun j => (W.φA ^ j) W.Q).prod with hJp
  have hYL : W.φA Y = Y * L := φ_prod W.φA W.X W.Q W.φA_X m
  refine ⟨m₀ + Multiset.card J, ?_⟩
  rw [GlobalTheory.NL.SandArb.map_mulLeft]
  have hdiv : W.X ^ m₀ * Jp ∣ (Y * L) ^ (m₀ + Multiset.card J) := by
    rw [mul_pow, pow_add, pow_add]
    refine (mul_dvd_mul (pow_dvd_pow_of_dvd (X_dvd W.φA W.X m) m₀) (multiset_dvd _ m J hJ)).trans ?_
    exact ⟨Y ^ Multiset.card J * L ^ m₀, by ring⟩
  obtain ⟨R, hR⟩ := hdiv
  set a := m₀ + Multiset.card J with ha
  have hb' : TWmap φR T b = E.jD T y + b := sub_eq_iff_eq_add.mp hb
  have hφc : TensorProduct.map φR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)
      (inclR (E.io Y) ^ a • b) =
      inclR (E.io (L ^ a)) • (inclR (E.io Y) ^ a • b) + inclR (E.io ((Y * L) ^ a)) • E.jD T y := by
    rw [map_smul_left, map_pow, ← hφ, hYL]
    change inclR (E.io (Y * L)) ^ a • TWmap φR T b = _
    rw [hb', smul_add, add_comm, smul_smul, map_pow, map_pow, map_pow, map_pow, map_mul, map_mul,
      mul_pow, mul_comm]
  have hw : inclR (E.io ((Y * L) ^ a)) • E.jD T y ∈
      LinearMap.range (TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)) := by
    obtain ⟨y', hy'⟩ := hm₀ _ hy
    rw [GlobalTheory.NL.SandArb.map_mulLeft, jD_smulA] at hy'
    rw [hR, map_mul, map_mul, map_mul, map_mul, mul_comm, mul_smul, mul_smul, map_pow, map_pow]
    refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ ?_
    rw [← hy']
    exact ⟨y', rfl⟩
  have key := mem_range_of_frob tb inclR φR hA (E.io (L ^ a)) _ _ hw hφc
  exact key

end Generic

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T → ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈ TAinf (inclR LL) T := by
  intro D HW F l _ K s LL h W E T hT J y hy b hb m hJ
  obtain ⟨m₀, hm₀, -⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  exact of_sand E (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.1
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) T
    (Module.Free.chooseBasis ↥(OL LL) ↥T.L.T) m₀ hm₀ J y hy b hb m hJ

end GlobalTheory.NL.FrobDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

section IntegralSpan

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_filD_zero : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
  have h0 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← map_one (algebraMap (Per.AinfP l) (Per.BdRp l)),
      GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    simp
  have h1 := GlobalTheory.RingIface.alg_mem_FilD_nat l h0
  rwa [map_one, Nat.cast_zero] at h1

theorem algebraMap_mem_filD_zero (u : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filD_zero

theorem equivFinsuppOfBasisLeft_map_id {O B B' ι : Type} [CommRing O] [Algebra ℤ_[l] O]
    [CommRing B] [CommRing B'] [Algebra ℤ_[l] B] [Algebra ℤ_[l] B']
    [DecidableEq ι] (b : Module.Basis ι ℤ_[l] O) (g : B →ₐ[ℤ_[l]] B') (r : O ⊗[ℤ_[l]] B) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id O O) g r) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b r k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul o β => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem equivFinsuppOfBasisRight_map_id {O R R' M κ : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M]
    [DecidableEq κ] (b : Module.Basis κ O M) (f : R →ₐ[O] R') (w : R ⊗[O] M) (j : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f.toLinearMap LinearMap.id w) j =
      f (TensorProduct.equivFinsuppOfBasisRight b w j) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem mem_span_filD_zero_of_iotaO_eq {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (r : OB l O) (s : OD l O) (h : iotaO O C r = dRO l O s) :
    r ∈ Submodule.span O
      {u : OB l O | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l 0 ∧ u = (1 : O) ⊗ₜ[ℤ_[l]] β} := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hr : r = (TensorProduct.equivFinsuppOfBasisLeft b r).sum fun k β => b k ⊗ₜ[ℤ_[l]] β := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hr, Finsupp.sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) ∈ Per.FilD l 0 := by
    have h1 := equivFinsuppOfBasisLeft_map_id b (iotaZ C) r k
    have h2 := equivFinsuppOfBasisLeft_map_id b (bdRpToBdR l) s k
    have h3 : Algebra.TensorProduct.map (AlgHom.id O O) (iotaZ C) r =
        Algebra.TensorProduct.map (AlgHom.id O O) (bdRpToBdR l) s := h
    rw [h3, h2] at h1
    have h4 : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) =
        algebraMap (Per.BdRp l) (Per.BdR l) (TensorProduct.equivFinsuppOfBasisLeft b s k) := h1.symm
    rw [h4]
    exact algebraMap_mem_filD_zero _
  have h5 : b k ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k) =
      b k • ((1 : O) ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hk, rfl⟩)

end IntegralSpan

theorem mem_span_filD_zero_of_integral : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
    (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T),
    TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) →
      w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T),
        C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ T C w hw
  classical
  obtain ⟨z, hz⟩ := hw
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  have hw' : w = (TensorProduct.equivFinsuppOfBasisRight bT w).sum fun j r => r ⊗ₜ[O] bT j := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hw', Finsupp.sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have hj : iotaO O C (TensorProduct.equivFinsuppOfBasisRight bT w j) =
      dRO l O (TensorProduct.equivFinsuppOfBasisRight bT z j) := by
    rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
    exact (congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) hz).symm
  have hr := mem_span_filD_zero_of_iotaO_eq C _ _ hj
  have hm := Submodule.mem_map_of_mem (f := (TensorProduct.mk O (OB l O) ↥T.L.T).flip (bT j)) hr
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨u, ⟨β, hβ, rfl⟩, rfl⟩
  exact ⟨β, bT j, hβ, rfl⟩

end GlobalTheory.BKGal.HatVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRoot
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.KunrDisj

theorem mem_Kunr_of_mem_Kur_of_mem_sup : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l →
    x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  intro l _ a e _ _ ϖ n x hxK hx
  have hN : 0 < l ^ n * e :=
    Nat.mul_pos (pow_pos (Fact.out : l.Prime).pos n) (Nat.pos_of_ne_zero (NeZero.ne e))
  have hπ : ϖ.seq n ^ (l ^ n * e) = -(l : Om l) := ϖ.seq_pow_mul n
  set U := Kunr l a with hU
  set π := ϖ.seq n with hπdef

  have hdeg := fun (E : Type) [Field E] [Algebra E (Om l)] (h : ∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) =>
    GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified l (l ^ n * e) π hN hπ E h
  have hint : ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) →
      IsIntegral E π := by
    intro E _ _ h
    by_contra hni
    have := hdeg E h
    rw [minpoly.eq_zero hni, Polynomial.natDegree_zero] at this
    omega
  let K2 : IntermediateField U (Om l) := IntermediateField.adjoin U {π}
  have hxK2 : x ∈ K2 := by
    have : x ∈ K2.restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact hx
    exact this
  let K1 : IntermediateField U (Om l) := IntermediateField.adjoin U {x}
  have hK1K2 : K1 ≤ K2 := IntermediateField.adjoin_simple_le_iff.2 hxK2
  have hUK : ∀ y : U, algebraMap U (Om l) y ∈ MaximalUnramifiedExtension l := fun y => Kunr_le_Kur l a y.2
  have hK1K : ∀ y : K1, algebraMap K1 (Om l) y ∈ MaximalUnramifiedExtension l := by
    intro y
    have hy : (y : Om l) ∈ K1.restrictScalars ℚ_[l] := y.2
    rw [IntermediateField.restrictScalars_adjoin] at hy
    refine (IntermediateField.adjoin_le_iff.2 ?_) hy
    rintro z (hz | hz)
    · exact Kunr_le_Kur l a hz
    · rw [Set.mem_singleton_iff.1 hz]; exact hxK

  let L : IntermediateField K1 (Om l) := IntermediateField.adjoin K1 {π}
  have hLK2 : L.restrictScalars U = K2 := by
    rw [IntermediateField.restrictScalars_adjoin]
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · exact hK1K2 hz
    · rw [Set.mem_singleton_iff.1 hz]; exact IntermediateField.mem_adjoin_simple_self U π
  have hK2r : Module.finrank U K2 = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint U hUK)]; exact hdeg U hUK
  have hLr : Module.finrank K1 L = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint K1 hK1K)]; exact hdeg K1 hK1K
  have hLU : Module.finrank U L = l ^ n * e := by
    rw [← hK2r, ← hLK2]; rfl
  have htower := Module.finrank_mul_finrank U K1 L
  rw [hLr, hLU] at htower
  have h1 : Module.finrank U K1 = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hN (htower.trans (one_mul _).symm)
    exact this
  have hbot : K1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  have : x ∈ K1 := IntermediateField.mem_adjoin_simple_self U x
  rw [hbot, IntermediateField.mem_bot] at this
  obtain ⟨y, rfl⟩ := this
  exact y.2

end GlobalTheory.KunrDisj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamilies
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem dpDen_mul_dvd_add (e i₁ i₂ n₁ n₂ : ℕ) :
    dpDen e i₁ n₁ * dpDen e i₂ n₂ ∣ dpDen e (i₁ + i₂) (n₁ + n₂) := by
  unfold dpDen
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add i₁ i₂
  have h2 : (n₁ / e).factorial * (n₂ / e).factorial ∣ ((n₁ + n₂) / e).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div n₁ n₂ e))
  have h3 := mul_dvd_mul h1 h2
  rwa [mul_mul_mul_comm] at h3

theorem mul_mem_QSet_of_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t x hx y hy
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', rfl⟩ := hy
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨fun p => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.2,
    ((dpDen e p.1 p.2 / (dpDen e q.1 r.1 * dpDen e q.2 r.2) : ℕ) : Wq l a) *
      (w (q.1, r.1) * w' (q.2, r.2)), ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, Pi.mul_apply, coeff_mul, map_sum, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [coeff_mul, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [coeff_ofW, coeff_ofW]
  simp only [map_mul, map_natCast]
  have hd := dpDen_mul_dvd_add e q.1 q.2 r.1 r.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hq, Finset.HasAntidiagonal.mem_antidiagonal.1 hr] at hd
  have h1 : (dpDen e q.1 r.1 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h2 : (dpDen e q.2 r.2 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h3 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  rw [Nat.cast_div hd (by push_cast; exact mul_ne_zero h1 h2)]
  push_cast
  field_simp

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRangeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonPlacePart_localBound_le_middleRange : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  first | exact @GlobalTheory.NLink.BBSize.main | exact GlobalTheory.NLink.BBSize.main | (intros; apply GlobalTheory.NLink.BBSize.main <;> assumption)
end

