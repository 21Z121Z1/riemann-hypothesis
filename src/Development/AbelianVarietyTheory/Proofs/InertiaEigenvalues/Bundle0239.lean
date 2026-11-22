import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanDOfFixed
section
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem mulR_mulR (a b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V a (mulR ℚ_[l] P.R.BdR LL V b x) = mulR ℚ_[l] P.R.BdR LL V (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp [mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem mulR_neg (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V (-a) x = -mulR ℚ_[l] P.R.BdR LL V a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, neg_zero]
  | tmul v c => simp [tmul_neg]
  | add y z hy hz => simp only [map_add, hy, hz, neg_add]

private theorem mulR_one (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem act_mulR (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K) ρ g (mulR ℚ_[l] P.R.BdR LL V a x) =
      mulR ℚ_[l] P.R.BdR LL V ((P.PD K).actdR g a) (actVdR (P.PD K) ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add, hy, hz]

private def spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) :
    AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR) where
  carrier := {y | ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
    (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, mulR ℚ_[l] P.R.BdR LL V (b i) (d i)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, b, d, hd, rfl⟩ ⟨n, b', d', hd', rfl⟩
    refine ⟨m + n, Fin.append b b', Fin.append d d', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hd j
      · rw [Fin.append_right]; exact hd' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  neg_mem' := by
    rintro _ ⟨m, b, d, hd, rfl⟩
    refine ⟨m, fun i => -b i, d, hd, ?_⟩
    simp only [mulR_neg, Finset.sum_neg_distrib]

private theorem mulR_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (a : P.R.BdR)
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    mulR ℚ_[l] P.R.BdR LL V a x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => a * b i, d, hd, ?_⟩
  simp only [map_sum, mulR_mulR]

private theorem act_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    actVdR (P.PD K) ρ g x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => (P.PD K).actdR g (b i), d, hd, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [act_mulR, (mem_DdR (P.PD K) ρ _).1 (hd i)]

private theorem mem_spanD_of_fixed {K K' : FinExt l} (h : K.1 ≤ K'.1)
    (ρ : Representation LL ↥(GK K) V) (x : V ⊗[ℚ_[l]] P.R.BdR)
    (hxH : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :
    x ∈ spanD P K ρ := by
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  haveI : Finite (GQ l ⧸ GK K') :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K'.1)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine JumpDescent.descent (Ω := Om l) ((GK K').subgroupOf (GK K))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) ?_ ?_
    (fun c => (mulR ℚ_[l] P.R.BdR LL V (algebraMap (Om l) P.R.BdR c)).toAddMonoidHom) ?_ ?_ ?_
    (fun g => ((g : GQ l) : Om l →* Om l)) (fun _ _ _ => rfl) (fun _ => rfl) ?_
    K'.1.toSubalgebra.toSubsemiring.toSubmonoid ?_
    ⊤ (spanD P K ρ) (fun _ _ _ => trivial) (fun _ _ _ => trivial) (act_mem_spanD P K ρ)
    (fun c => mulR_mem_spanD P K ρ _)
    (fun y _ hy' => ⟨1, fun _ => 1, fun _ => y, fun _ => (mem_DdR (P.PD K) ρ y).2 hy', by
      simp only [mulR_one, Fin.sum_univ_one]⟩) x trivial ?_
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro x
    simp only [map_one, LinearMap.toAddMonoidHom_coe, mulR_one]
  · intro g g' x
    simp only [map_mul, LinearMap.toAddMonoidHom_coe, mulR_mulR]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul v b => simp [add_mul, tmul_add]
    | add y z hy hz => simp only [map_add] at hy hz ⊢; rw [hy, hz]; abel
  · intro g c x
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [act_mulR, P.PD_actdR, P.actQdR_Om]
    rfl
  · intro g
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hg a ha => hg ⟨a, ha⟩, fun hg a => hg a.1 a.2⟩
  · intro g hg
    have := (mem_DdR (P.PD K') _ x).1 hxH ⟨g.1, hg⟩
    rw [JumpDescent.actVdR_comp P h] at this
    exact this

end

theorem spans_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V),
    Spans (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) → Spans (P.PD K) ρ := by
  intro l _ P K K' LL h V _ _ _ _ ρ hs y
  obtain ⟨m, b, d, hd, rfl⟩ := hs y
  exact (spanD P K ρ).sum_mem fun i _ =>
    mulR_mem_spanD P K ρ _ _ (mem_spanD_of_fixed P h ρ _ (hd i))

end GlobalTheory.DRFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
section
noncomputable section
namespace GlobalTheory.ThetaTie
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow {P : LocPrime l} (AI : LocAinf l P) (m n : ℕ) : AI.ζ (m + n) ^ l ^ n = AI.ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem isEps {P : LocPrime l} (AI : LocAinf l P) : IsEps (l := l) AI.ε := by
  constructor
  · refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
    have := zeta_pow AI 0 n
    rw [zero_add, AI.ζ_zero] at this
    rw [this]
  · have : ((frobeniusEquiv (Per.Fl l) l).symm AI.ε).untilt = AI.ζ 1 := by
      refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
      refine ⟨AI.ζ (1 + n), ?_, ?_⟩
      · rw [add_comm]
        exact (AI.ε_coeff (n + 1)).symm.trans (PreTilt.coeff_frobeniusEquiv_symm n _).symm
      · rw [zeta_pow AI 1 n]
    rw [this]
    exact AI.ζ_one

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  have : Subsingleton (Per.AinfP l ⧸ Per.kerP l ^ 0) := by
    rw [pow_zero, Ideal.one_eq_top]; infer_instance
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 0 y).2 (Subsingleton.elim _ _)

theorem mem_filD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact GlobalTheory.RingIface.exists_of_mem_FilD_nat l
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem alg_inj {e : Per.Fl l} (he : IsEps e) :
    Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := by
  have _ := he
  exact (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem log_mu {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have hm : algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
    refine GlobalTheory.RingIface.alg_mem_kerP l ?_
    rw [map_sub, WittVector.fontaineTheta_teichmuller, he.1, map_one, sub_self]
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  change Per.ev l 2 (algebraMap (Per.AinfP l) (Per.BdRp l)
    (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) - y) = 0
  rw [map_sub, ev_alg]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = m at hm h ⊢
  have h2 : Ideal.Quotient.mk (Per.kerP l ^ 2) (m ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hm 2)
  have hu : IsUnit ((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  have hs : (∑ k ∈ Finset.range 2, (-1) ^ k * (((2 : ℕ).factorial / (k + 1) : ℕ) : Per.AinfP l) *
      m ^ (k + 1)) = ((2 : ℕ) : Per.AinfP l) * m - m ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hs, map_sub, h2, sub_zero, map_mul, map_natCast] at h
  rw [sub_eq_zero]
  exact (hu.mul_left_cancel h).symm

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem eD_ιA (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  refine Eq.trans ?_ h
  simp

theorem fil_nat (n : ℕ) (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil n ↔
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (T.fil _ _ _).trans (mem_filD_nat n _)

theorem fil_zero (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil 0 ↔
    ∃ z, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (fil_nat T 0 x).trans ⟨fun ⟨z, _, h⟩ => ⟨z, h⟩, fun ⟨z, h⟩ => ⟨z, mem_filtration_zero' z, h⟩⟩

def th (x : P.R.BdR) : ℂ_[l] :=
  Per.θD l (Function.invFun (algebraMap (Per.BdRp l) (Per.BdR l)) (T.eD x))

theorem th_eq {x : P.R.BdR} {z : Per.BdRp l}
    (h : algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x) : th T x = Per.θD l z := by
  rw [th, ← h, Function.leftInverse_invFun (alg_inj (isEps AI))]

include T in
theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD (botExt l)).Fil (-1), P.ιB P.tB * s = 1 := by
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l _ (isEps AI)
  obtain ⟨-, hk, hun, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hu := (P.PD (botExt l)).t_unit
  have t1 := (P.PD (botExt l)).mem_filtration_one
  have t2 := (P.PD (botExt l)).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at t1 t2
  rw [P.period_datum_t_eq] at hu
  obtain ⟨s, hs⟩ := (hu.map P.ιB).exists_right_inv
  refine ⟨s, ?_, hs⟩
  obtain ⟨z, hz, ez⟩ := (fil_nat T 1 _).1 t1
  obtain ⟨u, rfl⟩ := (h1 1 z).1 hz
  have huu : IsUnit u := hun u fun h0 => by
    obtain ⟨w, rfl⟩ := (h1 1 u).1 ((hk u).1 h0)
    exact t2 ((fil_nat T 2 _).2 ⟨_, (h1 2 _).2 ⟨w, by ring⟩, ez⟩)
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  rw [T.fil, GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l _ (isEps AI)]
  refine ⟨v, ?_⟩
  have e1 : T.eD (P.ιB P.tB) * T.eD s = 1 := by rw [← map_mul, hs, map_one]
  have e2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv
  rw [← ez] at e1
  rw [show (- (-1 : ℤ)).toNat = 1 from rfl, show (-1 : ℤ).toNat = 0 from rfl]
  simp only [map_mul, map_one, pow_one, pow_zero, one_mul] at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi AI.ε)) = X at e1 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) u = U at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) v = V at e2 ⊢
  linear_combination V * e1 - (T.eD s * X) * e2

def thetaL : ThetaL P AI where
  θ := th T
  θ_one := by rw [th_eq T (z := 1) (by simp), map_one]
  θ_add x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a + b) (by rw [map_add, map_add, ha, hb]), map_add]
  θ_mul x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a * b) (by rw [map_mul, map_mul, ha, hb]), map_mul]
  θ_onto c := by
    obtain ⟨z, hz⟩ := (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).1 c
    have e : algebraMap (Per.BdRp l) (Per.BdR l) z =
        T.eD (T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) z)) := (T.eD.apply_symm_apply _).symm
    exact ⟨_, (fil_zero T _).2 ⟨z, e⟩, (th_eq T e).trans hz⟩
  θ_ker x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    rw [th_eq T ha, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1]
    refine ⟨fun h => (fil_nat T 1 x).2 ⟨a, h, ha⟩, fun h => ?_⟩
    obtain ⟨z, hz, e⟩ := (fil_nat T 1 x).1 h
    rwa [← alg_inj (isEps AI) (e.trans ha.symm)]
  θ_act g x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    have e : algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g a) = T.eD (P.actQdR g x) := by
      rw [T.actD, ← ha]
      exact (GlobalTheory.RingIface.sigD_alg l g a).symm
    rw [th_eq T ha, th_eq T e, actC_eq, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2]
  θ_Om x := by
    obtain ⟨y, h1, h2⟩ := T.om x
    rw [th_eq T h1.symm, h2]
  θ_int a := by
    rw [th_eq T (eD_ιA T a).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  θ_teich x y h := by
    rw [th_eq T (eD_ιA T _).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, WittVector.fontaineTheta_teichmuller]
    have h1 := Ideal.Quotient.eq.1 ((PreTilt.mk_untilt_eq_coeff_zero x).trans h)
    have h2 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
    simpa using h2
  fil_succ_iff_mul_t a x := by
    have t1 := (P.PD (botExt l)).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at t1
    constructor
    · intro hx
      obtain ⟨s, hs, e⟩ := exists_inverse_fontaineElement_mem_fil_neg_one T
      refine ⟨s * x, ?_, by rw [← mul_assoc, e, one_mul]⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ hs hx
      rwa [show -1 + (a + 1) = a by ring] at this
    · rintro ⟨y, hy, rfl⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ t1 hy
      rwa [add_comm] at this
  t_μ := by
    obtain ⟨y, hy, e⟩ := T.t
    refine (fil_nat T 2 _).2 ⟨_, log_mu (isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, eD_ιA]
    rfl

theorem nonempty_thetaL (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] :
    Nonempty (ThetaL (D.loc l) (D.locA l)) :=
  ⟨thetaL (D.locT l)⟩

end GlobalTheory.ThetaTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAutLeOneIff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.EigenCoord

theorem exists_basis_mem_iff {O L V : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] [AddCommGroup V] [Module L V] [Module O V] [IsScalarTower O L V]
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span L (T : Set V) = ⊤) :
    ∃ (ρ : ℕ) (t : Module.Basis (Fin ρ) L V),
      ∀ v, v ∈ T ↔ ∀ i, ∃ o : O, algebraMap O L o = t.repr v i := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let c := Module.finBasis O T
  have hli : LinearIndependent O (fun i => (c i : V)) :=
    c.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli' : LinearIndependent L (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing O L).mp hli
  have hsum : ∀ x : T, (x : V) = ∑ i, algebraMap O L (c.repr x i) • (c i : V) := by
    intro x
    have h := congrArg T.subtype (c.sum_repr x)
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    simp only [algebraMap_smul]
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => (c i : V)) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, show x = ((⟨x, hx⟩ : T) : V) from rfl, hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let t := Module.Basis.mk hli' hsp
  have ht : ∀ i, t i = (c i : V) := fun i => Module.Basis.mk_apply hli' hsp i
  refine ⟨_, t, fun v => ⟨fun hv i => ⟨c.repr ⟨v, hv⟩ i, ?_⟩, fun h => ?_⟩⟩
  · have h1 : v = ∑ j, algebraMap O L (c.repr ⟨v, hv⟩ j) • t j := by
      simp only [ht]
      exact hsum ⟨v, hv⟩
    have h2 := congrFun (t.repr_sum_self (fun j => algebraMap O L (c.repr ⟨v, hv⟩ j))) i
    rw [← h1] at h2
    exact h2.symm
  · choose o ho using h
    rw [← t.sum_repr v]
    refine T.sum_mem fun i _ => ?_
    rw [← ho, algebraMap_smul, ht]
    exact T.smul_mem _ (c i).2

theorem norm_coe_aut_le_one_iff {l : ℕ} [Fact l.Prime] (ι : GQ l) (x : Om l) :
    ‖((ι x : Om l) : PadicComplex l)‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_extends, ← isIntegral_padicInt_iff_norm_le_one,
    ← isIntegral_padicInt_iff_norm_le_one]
  exact isIntegral_algHom_iff (ι.toAlgHom.restrictScalars ℤ_[l]) ι.injective

theorem exists_matrix_of_basis {F L C V : Type} [NormedField F] [Field L] [NormedField C]
    [Algebra F L] [Algebra F C] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (S : Set V) {d ρ : ℕ} (b : Module.Basis (Fin d) F V) (t : Module.Basis (Fin ρ) L V)
    (φ : L →ₐ[F] C) (hb : ∀ v, v ∈ S ↔ ∀ i, ‖b.repr v i‖ ≤ 1)
    (hmem : ∀ v, v ∈ S ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1) :
    ∃ Pr : Matrix (Fin ρ) (Fin d) C, (∀ i j, ‖Pr i j‖ ≤ 1) ∧
      (∀ a : L, Pr * Matrix.of (fun i k : Fin d => algebraMap F C (b.repr (a • b k) i)) =
        φ a • Pr) ∧
      ∀ y : Fin d → F, (∀ i, ‖Pr.mulVec (fun a => algebraMap F C (y a)) i‖ ≤ 1) →
        ∀ a, ‖y a‖ ≤ 1 := by
  have key : ∀ (y : Fin d → F) (i : Fin ρ),
      ∑ j, φ (t.repr (b j) i) * algebraMap F C (y j) = φ (t.repr (∑ j, y j • b j) i) := by
    intro y i
    rw [map_sum, Finsupp.finset_sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul L (y j), map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      AlgHom.commutes, mul_comm]
  refine ⟨Matrix.of fun i j => φ (t.repr (b j) i), fun i j => ?_, fun a => ?_, fun y hy a => ?_⟩
  · refine (hmem _).mp ((hb _).mpr fun k => ?_) i
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.smul_apply]
    rw [key, b.sum_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
  · have hv : (∑ j, y j • b j) ∈ S := by
      refine (hmem _).mpr fun i => ?_
      rw [← key]
      exact hy i
    have := (hb _).mp hv a
    rwa [congrFun (b.repr_sum_self y) a] at this

theorem exists_matrix : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V), (∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1) → ∀ ι : GQ l, ∃ (ρ : ℕ) (Pr : Matrix (Fin ρ) (Fin d) (PadicComplex l)), (∀ i j, ‖Pr i j‖ ≤ 1) ∧ (∀ a : ↥LL.1, Pr * Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i)) = ((ι (a : Om l) : Om l) : PadicComplex l) • Pr) ∧ ∀ y : Fin d → ℚ_[l], (∀ i, ‖Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) i‖ ≤ 1) → ∀ a, ‖y a‖ ≤ 1 := by
  intro l _ K LL T d b hb ι
  haveI := LL.2
  haveI : IsFractionRing (OL LL) LL.1 := isFractionRing_integralClosure_padicInt l LL.1
  obtain ⟨ρ, t, ht⟩ := exists_basis_mem_iff (L := LL.1) T.L.T T.L.fg T.L.free T.L.span
  let φ : LL.1 →ₐ[ℚ_[l]] PadicComplex l :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp (ι.toAlgHom.comp LL.1.val)
  have hφ : ∀ x : LL.1, φ x = ((ι (x : Om l) : Om l) : PadicComplex l) := fun _ => rfl
  have hmem : ∀ v, v ∈ T.L.T ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1 := by
    intro v
    rw [ht]
    refine forall_congr' fun i => ?_
    rw [hφ, norm_coe_aut_le_one_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨fun ⟨o, ho⟩ => ho ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  exact ⟨ρ, exists_matrix_of_basis (T.L.T : Set T.V) b t φ hb hmem⟩

end GlobalTheory.EigenCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSubSubMemXiOfMonodromyEq
section
open PowerSeries GlobalTheory.BK

theorem GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy σ hσ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hyl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hy⟩
  obtain ⟨⟨s, -, -, hs, d, -, hd⟩, -⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D y hyl
  have h0 : D.conn (σ - s) = 0 := by rw [map_sub, hσ, hs, sub_self]
  set w := D.xiExt.symm (σ - s) with hw
  have hder : derV w = 0 := by
    have h1 : D.conn (D.xiExt w) = 0 := by rw [hw, LinearEquiv.apply_symm_apply]; exact h0
    rw [PhiMod.conn_apply, PhiMod.nabla_xiExt] at h1
    have h2 : D.xiExt (derV w) = 0 :=
      smul_right_injective (Vec K a ι) (X_ne_zero (R := K)) (by simpa only [smul_zero] using h1)
    exact D.xiExt.map_eq_zero_iff.1 h2
  have hwc : w = cst (red w) := by
    ext τ i n
    have h3 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
    rw [derV_apply, coeff_derivative] at h3
    rcases n with _ | n
    · simp [red_apply, red0]
    · have h4 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
      rw [derV_apply, coeff_derivative] at h4
      simp only [Pi.zero_apply, map_zero, mul_eq_zero] at h4
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      rcases h4 with h4 | h4
      · exact h4
      · exact absurd h4 (by exact_mod_cast Nat.succ_ne_zero n)
  have hxi : σ - s = D.xi (red w) := by
    rw [PhiMod.xi_apply, ← hwc, hw, LinearEquiv.apply_symm_apply]
  refine ⟨d + D.phiD (red w) - red w, ?_⟩
  rw [map_sub, map_add, ← PhiMod.phi_xi, ← hxi, ← hd, map_sub]
  abel
end

