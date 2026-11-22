import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0581
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

theorem fr_mul_of_fixed (r N : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (h : fr l r c = c) : fr l (r * N) c = c := by
  induction N with
  | zero => simp [fr]
  | succ k ih =>
    change (frobUr l ^ (r * (k + 1))) c = c
    rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]
    change (frobUr l ^ (r * k)) (fr l r c) = c
    rw [h]
    exact ih

theorem isRat_twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (r N : ℕ) (hN : 0 < N) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (hρ : IsRat r ρ)
    (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l (r * N) c = c → (c : Om l) ∈ K'.1) (hfr : ∀ g, fr l (r * N) (χ g : ↥(MaximalUnramifiedExtension l)) = χ g)
    (hcont : Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) :
    IsRat (r * N) (twist hK ρ χ a) := ⟨Nat.mul_pos hρ.pos hN, hle, fun g i j => by
    rw [twist_val, Matrix.smul_apply, smul_eq_mul, map_mul, fr_mul_of_fixed r N _ (hρ.rat _ i j),
      Units.val_zpow_eq_zpow_val, map_zpow₀, hfr], fun i j => by
    have h1 : Continuous fun g : ↥(GK K') => (((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) :=
      (hρ.cont i j).comp (continuous_subtype_val.subtype_mk _)
    have h2 : Continuous fun g : ↥(GK K') => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l) ^ a :=
      hcont.zpow₀ _ fun g => Or.inl (by
        intro h0
        exact (χ g).ne_zero (Subtype.ext h0))
    refine (h2.mul h1).congr fun g => ?_
    simp only [twist_val, Matrix.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val]
    push_cast
    rfl⟩

theorem potentiallySemistable_of_lubinTateTwist (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ)
    (hact : ∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) :
    AdmSt P (twist hK ρ χ a) → AdmSt P ρ := by
  have msmul : ∀ {R S : Type} [CommRing R] [CommRing S] {F : Type} [FunLike F R S] [RingHomClass F R S] (f : F) (c : R)
      (M : Matrix n n R), (c • M).map f = f c • M.map f := fun f c M => by
    ext i j; simp
  rintro ⟨K'', hK'', Q', hQ'⟩
  refine ⟨K'', hK.trans hK'', scalGL n (Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (x ^ a)) * Q', fun g => ?_⟩
  have hg := hQ' g
  rw [twist_val, msmul, Matrix.smul_mul] at hg
  set g' : ↥(GK K') := ⟨(g : GQ l), GK_le hK'' g.2⟩
  have hx : Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x =
      Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') * x := by
    apply Units.ext
    simpa using hact g'
  have hxa : actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) =
      ks P ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) * Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) := by
    have h2 := congrArg (fun u : P.R.Bˣ => Polynomial.C ((u ^ a : P.R.Bˣ) : P.R.B)) hx
    have e1 : ((Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x ^ a : P.R.Bˣ) : P.R.B) =
        P.actQ (g : GQ l) ((x ^ a : P.R.Bˣ) : P.R.B) := by rw [← map_zpow]; rfl
    have e2 : ((Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') ^ a : P.R.Bˣ) : P.R.B) =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) := by rw [← map_zpow]; rfl
    simp only [mul_zpow] at h2
    rw [e1, Units.val_mul, e2, map_mul] at h2
    rw [actSt_C]
    exact h2
  rw [scalGL_mul_val, msmul, Matrix.mul_smul, Units.coe_map]
  change actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) • _ =
    Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) • _
  rw [hxa]
  conv_rhs => rw [← hg]
  rw [smul_smul, mul_comm (Polynomial.C _)]

omit [DecidableEq n] in
theorem sum_weights (r N : ℕ) (hr : 0 < r) (w : Fin r → n → ℤ) (hN : Fintype.card n = N) :
    ∑ m : Fin (r * N), ∑ j, (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then -∑ m, ∑ j, w m j else 0) = 0 := by
  subst hN
  simp only [Finset.sum_add_distrib]
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range (r * N), (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) i =
      N * ∑ m, ∑ j, w m j := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have : ∑ x ∈ Finset.range r, (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x) =
          ∑ m, ∑ j, w m j := by
        rw [← Fin.sum_univ_eq_sum_range (fun x => (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x))]
        refine Finset.sum_congr rfl fun m _ => ?_
        have e : (⟨(r * k + (m : ℕ)) % r, Nat.mod_lt _ hr⟩ : Fin r) = m := by
          apply Fin.ext
          simp only
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.2]
        simp only [e]
      rw [this]
      push_cast
      ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j), key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i = 0 then -∑ m, ∑ j, w m j else 0),
    Finset.sum_ite_eq' (Finset.range _) 0]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · simp [h0]
  · rw [if_pos (Finset.mem_range.mpr (Nat.mul_pos hr h0))]
    ring

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon

theorem twistStep : TwistStep := by
  intro l _ P AI T n _ _ K r ρ w hρ hw
  by_cases hn : Fintype.card n = 0
  · refine ⟨K, r, ρ, w, hρ, hw, ?_, id⟩
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hN : 0 < Fintype.card n := Nat.pos_of_ne_zero hn
    have hs : 0 < r * Fintype.card n := Nat.mul_pos hρ.pos hN
    obtain ⟨K', hK, x, χ, hle, hfr, hcont, hact, h1, h2, hj⟩ := GlobalTheory.T.exists_lubinTate_character_unramified_period l P AI T K (r * Fintype.card n) hs
    exact ⟨K', r * Fintype.card n, Twist.twist hK ρ χ (-∑ m, ∑ j, w m j), _,
      Twist.isRat_twist hK r _ hN ρ χ _ hρ hle hfr hcont,
      GlobalTheory.T.hasHodgeTateWeightFrame_character_twist l P AI T n K K' hK r (Fintype.card n) hρ.pos ρ w χ x _ hρ hw hact h1 h2 hj,
      Twist.sum_weights r _ hρ.pos w rfl, Twist.potentiallySemistable_of_lubinTateTwist P hK ρ χ x _ hact⟩

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGammaStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wach_of_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.CocycleInj.main | exact GlobalTheory.NL.CocycleInj.main | (intros; apply GlobalTheory.NL.CocycleInj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensor
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisInt

theorem tw_incl_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem tw_incl_comp {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' R'' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R'']
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G Qp LL O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a t => simp [TWincl]

theorem mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hLM hML jB hcmp ε hε z
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hK := (GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hLM hML ε δ hε hδ).2.2.2
  have step1 : ∀ c : ι → OA l O, ∃ y : TW (OA l O) T,
      jB (fun i => toB l O (((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) * c i)) = TWincl (toB l O) T y := by
    intro c
    obtain ⟨y, hy⟩ := hK (inclL t ϖ P c) ⟨c, rfl⟩
    refine ⟨y, hcmp _ y ?_⟩
    rw [← hy]
    congr 1
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [map_mul, Algebra.TensorProduct.tmul_pow]
  choose y hy using fun i : ι => step1 (Pi.single i 1)
  refine ⟨∑ i, z i • TWincl (toOCr l O) T (y i), ?_⟩
  have hsingle : ∀ i, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (Pi.single i 1) =
      TWincl (toB l O) T (y i) := by
    intro i
    rw [← hy i, ← map_smul]
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hz : (fun i => toOB l O (z i)) = ∑ i, toOB l O (z i) • (Pi.single i (1 : OB l O)) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hz, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, hsingle, tw_incl_smul, tw_incl_comp]
  rfl

end GlobalTheory.BKGal.CrisInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  first | exact @GlobalTheory.BSP.norm_hf_g_X_and_φ_le | exact GlobalTheory.BSP.norm_hf_g_X_and_φ_le | (intros; apply GlobalTheory.BSP.norm_hf_g_X_and_φ_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfLt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK GlobalTheory.Prism

namespace GlobalTheory.PZ.TiltHyps

theorem two_le_resCard {l : ℕ} [Fact l.Prime] (K : FinExt l) : 2 ≤ resCard K := by
  unfold resCard
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  have : 0 < Module.finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  calc 2 ≤ l := (Fact.out : l.Prime).two_le
    _ = l ^ 1 := (pow_one l).symm
    _ ≤ _ := Nat.pow_le_pow_right (Fact.out : l.Prime).pos this

theorem norm_le_one_of_lt {l : ℕ} [Fact l.Prime] {c w : ℂ_[l]} {q : ℕ} (hq : 2 ≤ q) (hc : ‖c‖ ≤ 1)
    (h : ‖c * w + w ^ q‖ ≤ 1) : ‖w‖ ≤ 1 := by
  by_contra hw
  push_neg at hw
  have e : w ^ q = (c * w + w ^ q) + (-(c * w)) := by ring
  have h1 : ‖w ^ q‖ ≤ max ‖c * w + w ^ q‖ ‖-(c * w)‖ := by
    have := IsUltrametricDist.norm_add_le_max (c * w + w ^ q) (-(c * w))
    rwa [← e] at this
  have h2 : ‖-(c * w)‖ ≤ ‖w‖ := by
    rw [norm_neg, norm_mul]; nlinarith [norm_nonneg w, norm_nonneg c]
  have h3 : ‖w‖ ^ 2 ≤ ‖w‖ ^ q := pow_le_pow_right₀ hw.le hq
  rw [norm_pow] at h1
  have h4 : ‖w‖ ^ q ≤ ‖w‖ := h1.trans (max_le (h.trans hw.le) h2)
  nlinarith

end GlobalTheory.PZ.TiltHyps

open GlobalTheory.PZ GlobalTheory.PZ.TiltHyps in
theorem GlobalTheory.PZ.ltData_tilt_hyps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) [Finite (IsLocalRing.ResidueField ↥(OL K))] (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ (hπ : Irreducible π) (hF : IsLubinTateSeries π (ltSeries K π)) (v : ℕ → OC l),
      (∀ n, ((v n : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n)) ∧
      (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i (ltSeries K π)) * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l])) ∧
      v 0 = 0 ∧ v 1 ≠ 0 ∧
      ∀ (g : ↥(GK K)) (u : ↥(OL K)), (u : ↥K.1) = (χ g : ↥K.1) → ∀ n,
        HasSum (fun i => ((intToOC K (PowerSeries.coeff i (lubinTateHom hπ hF hF u).toPowerSeries) * v n ^ i : OC l) : ℂ_[l]))
          ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  intro l _ K _ χ π z h
  obtain ⟨hπ, hz0, hz1, hrel, hgal⟩ := h
  obtain ⟨hF, hiff⟩ := GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ
  set q := resCard K with hqdef
  have hq : 2 ≤ q := two_le_resCard K
  set c : ℂ_[l] := (((π : ↥K.1) : Om l) : ℂ_[l]) with hcdef
  have hc : ‖c‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 (intToOC K π).2
  have hrelC : ∀ n, c * (z (n + 1) : ℂ_[l]) + (z (n + 1) : ℂ_[l]) ^ q = (z n : ℂ_[l]) := fun n => by
    have := congrArg (algebraMap (Om l) ℂ_[l]) (hrel n)
    rw [map_add, map_mul, map_pow] at this; exact this
  have hnorm : ∀ n, ‖(z n : ℂ_[l])‖ ≤ 1 := by
    intro n
    induction n with
    | zero => rw [hz0]; simp
    | succ n ih => exact norm_le_one_of_lt hq hc (by rw [hrelC n]; exact ih)
  let v : ℕ → OC l := fun n => ⟨(z n : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 (hnorm n)⟩
  refine ⟨hπ, hF, v, fun n => rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    have hcoef : ∀ i, ((intToOC K (PowerSeries.coeff i (ltSeries K π)) * v (n + 1) ^ i : OC l) : ℂ_[l]) =
        (if i = 1 then c * (z (n + 1) : ℂ_[l]) else 0) + (if i = q then (z (n + 1) : ℂ_[l]) ^ q else 0) := by
      intro i
      have e1 : ltSeries K π = PowerSeries.C π * PowerSeries.X ^ 1 + PowerSeries.X ^ q := by
        rw [pow_one]; rfl
      rw [e1, map_add, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow]
      split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | (subst_vars; simp [v, hcdef, coe_intToOC])
    simp_rw [hcoef]
    show HasSum _ (z n : ℂ_[l])
    rw [← hrelC n]
    exact (hasSum_ite_eq 1 _).add (hasSum_ite_eq q _)
  · exact Subtype.ext (by simp [v, hz0])
  · intro h1
    apply hz1
    have : (z 1 : ℂ_[l]) = ((0 : Om l) : ℂ_[l]) := by
      simpa [v] using congrArg Subtype.val h1
    exact (algebraMap (Om l) ℂ_[l]).injective this
  · intro g u hu n
    obtain ⟨a, ha, φ, hφ, hs⟩ := hgal g
    have hau : a = u := Subtype.ext (ha.trans hu.symm)
    subst hau
    have hφe : φ = (lubinTateHom hπ hF hF a).toPowerSeries := (hiff a φ).1 hφ
    rw [← hφe]
    have hm := (hs n).map (algebraMap (Om l) ℂ_[l]).toAddMonoidHom
      (UniformSpace.Completion.continuous_coe (Om l))
    have e2 : ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) = (((g : GQ l) (z n) : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (v n)).trans ?_
      change Per.σC (g : GQ l) ((z n : Om l) : ℂ_[l]) = _
      rw [GlobalTheory.RingBasics.σC_coe]
    rw [e2]
    convert hm using 1
    funext i
    show (((intToOC K _ : OC l) : ℂ_[l]) * ((z n : Om l) : ℂ_[l]) ^ i) = _
    simp only [Function.comp, coe_intToOC, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, map_pow]
    rfl
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.JumpsSES

section Trivial

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  induction b, h using Int.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

theorem one_not_mem_fil_one : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

theorem ddR_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K BdR).toLinearMap) ∧
    (∀ a ≤ 0, x ∈ FilV PD (LL := LL) (V := V) a) ∧
    (∀ a, 1 ≤ a → x ∈ FilV PD (LL := LL) (V := V) a → x = 0) := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  let e := Module.finBasis Qp V
  let c : Fin (finrank Qp V) → V ⊗[Qp] BdR →ₗ[Qp] BdR := fun i =>
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (LinearMap.rTensor BdR (e.coord i))
  have hsum : ∀ y : V ⊗[Qp] BdR, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
  have hc : ∀ i g y, c i (actVdR PD ρ g y) = PD.actdR g (c i y) := by
    intro i g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have := ((PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
      have h2 : PD.actdR g (e.coord i v • b) = e.coord i v • PD.actdR g b := this
      simp only [c, actVdR, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2, hρ]
      simp
    | add a b ha hb => simp only [map_add, ha, hb]
  have hk : ∀ i, ∃ k : K, algebraMap K BdR k = c i x := fun i =>
    PD.invdR (c i x) fun g => by rw [← hc, hx]
  refine ⟨?_, fun a ha => ?_, fun a ha hF => ?_⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    have : c i x ∈ PD.Fil a := by
      rw [← hk, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (fil_anti PD ha PD.one_mem)
    exact ⟨e i ⊗ₜ ⟨c i x, this⟩, by simp⟩
  · have hF' : ∀ i, ∀ y ∈ FilV PD (LL := LL) (V := V) a, c i y ∈ PD.Fil a := by
      rintro i _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : (e.coord i v) • (b : BdR) ∈ (PD.Fil a).restrictScalars Qp := Submodule.smul_mem _ _ b.2
        simpa [c] using this
      | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz
    rw [hsum x]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    by_cases h0 : k = 0
    · rw [← hk, h0]; simp
    · exfalso
      apply one_not_mem_fil_one PD
      have h1 := Submodule.smul_mem _ k⁻¹ (fil_anti PD ha (hF' i x hF))
      rwa [← hk, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h0, one_smul] at h1

theorem jumps_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ) (ha : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply ha
  ext x
  simp only [FildR, Submodule.mem_inf]
  refine and_congr_right fun hx => ?_
  obtain ⟨-, h1, h2⟩ := ddR_of_trivial PD ρ hρ x hx.1
  rcases lt_or_gt_of_ne h0 with h | h
  · exact ⟨fun _ => h1 a (by omega), fun _ => h1 (a + 1) (by omega)⟩
  · constructor
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _

end Trivial

theorem jumps_ses_and_one : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsSESLat (Qp := ℚ_[l]) ι π → (∀ τ a, IsJumpV ((D.loc l).PD K) T₁.ρ τ a ↔ IsJumpV ((D.loc l).PD K) T₀.ρ τ a ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) ∧ ∀ τ a, IsJumpV ((D.loc l).PD K) W.one.ρ τ a → a = 0 := by
  intro D HW l _ K s LL h W T₀ T₁ T₂ ι π hc hS
  refine ⟨fun τ a => ?_, fun τ a ha => ?_⟩
  · have h0 : IsCrys ((D.loc l).PD K) T₀.ρ :=
      (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hS.1 hc
    have h2 : IsCrys ((D.loc l).PD K) T₂.ρ :=
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2
        hS.2.1 hc).1
    exact GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l _ _ (D.locT l) K LL T₀ T₁ T₂ ι π hS h0 hc h2 τ a
  · haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] W.one.V := Module.Finite.trans ↥LL.1 W.one.V
    exact jumps_of_trivial _ W.one.ρ W.one_triv τ a ha

end GlobalTheory.NL.JumpsSES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDetStatement
section
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet : ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  first | exact @GlobalTheory.dU_eq_const_mul_det_topL_translate | exact GlobalTheory.dU_eq_const_mul_det_topL_translate | (intros; apply GlobalTheory.dU_eq_const_mul_det_topL_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodCocycleFrobeniusRelationOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_cocycle_frobenius_relation_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap WittVector.frobenius Φ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ := by
  first | (exact @GlobalTheory.BKLim.KappaFrob.main) | (exact GlobalTheory.BKLim.KappaFrob.main) | (intros; apply GlobalTheory.BKLim.KappaFrob.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap WittVector.frobenius Φ → IsDiscMap bk.ev i → IsDiscMap (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  first | (exact @GlobalTheory.BKLim.FrobTwistKappa.main) | (exact GlobalTheory.BKLim.FrobTwistKappa.main) | (intros; apply GlobalTheory.BKLim.FrobTwistKappa.main  <;> assumption)
end

