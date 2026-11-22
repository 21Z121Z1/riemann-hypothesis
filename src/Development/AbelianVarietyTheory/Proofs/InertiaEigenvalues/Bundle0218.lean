import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0210
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFGTopPPowInverseLatticeStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFGTop_p_pow_inverse_lattice : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  first | exact @GlobalTheory.isFGTop_comap_lsmul_one | exact GlobalTheory.isFGTop_comap_lsmul_one | (intros; apply GlobalTheory.isFGTop_comap_lsmul_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicMonodromyPolynomialsRaiseDegreeStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Degrees O K l e a := by
  first | exact @GlobalTheory.DegreeRaise.main | exact GlobalTheory.DegreeRaise.main | (intros; apply GlobalTheory.DegreeRaise.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapH2SubtypeInjectiveStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_H2_subtype_injective : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ (hfg : ∀ n, IsFGTop O (N n)) (n : ℕ),
      Function.Injective (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)) := by
  first | exact @GlobalTheory.map_H2_subtype_injective_of_union | exact GlobalTheory.map_H2_subtype_injective_of_union | (intros; apply GlobalTheory.map_H2_subtype_injective_of_union <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfPowSmulMem
section
noncomputable section

namespace GlobalTheory.WachSat

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_pow_smul_le {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (c : O) (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L S : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (hS : S.FG) :
    ∃ m : ℕ, ∀ x ∈ S, c ^ m • x ∈ L := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_7 h_8 h_9 h_10; revert LL O h_2 h_3 h_4 h_5 V h_7 h_8 h_9 h_10 c hc L S hL hS; exact @_root_.GlobalTheory.PowerScalarMembership.main)
  | exact @_root_.GlobalTheory.PowerScalarMembership.main
  | exact _root_.GlobalTheory.PowerScalarMembership.main
  | (apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScalarMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScalarMembership.main ..)

variable (W : LocWach PD LL O v n)

theorem ee_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (x : W.EE)
    (hx : (PD.p : W.EE) * x = 0) : x = 0 := by
  have hA : ∀ a : LetA O n, (PD.p : LetA O n) * a = 0 → a = 0 := by
    intro a ha
    funext i
    ext k
    have h1 : (PD.p : PowerSeries O) * a i = 0 := congrFun ha i
    have h2 := congrArg (PowerSeries.coeff k) h1
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, map_zero] at h2
    simpa using hp _ h2
  haveI := W.EE_complete
  refine IsHausdorff.haus (I := Ideal.span {((PD.p : ℕ) : W.EE)}) inferInstance x fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨a, m, ha⟩ := W.EE_dense x k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b, hb⟩ := W.EE_sat ((PD.p : LetA O n) * a) (k + 1) (by
    refine Ideal.mem_span_singleton'.2 ⟨-y, ?_⟩
    rw [map_mul, map_natCast]
    linear_combination (-(PD.p : W.EE)) * hy - (algebraMap (LetA O n) W.EE (letπ ^ m)) * hx)
  have hab : a = (PD.p : LetA O n) ^ k * b := by
    have := hA (a - (PD.p : LetA O n) ^ k * b) (by rw [mul_sub, hb]; ring)
    exact sub_eq_zero.1 this
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ m)) := by
    rw [map_pow]; exact W.EE_π.pow m
  refine Ideal.mem_span_singleton'.2 ⟨(y + algebraMap (LetA O n) W.EE b) * ↑u⁻¹, ?_⟩
  rw [hab, map_mul, map_pow (algebraMap (LetA O n) W.EE) (PD.p : LetA O n), map_natCast, ← hu] at hy
  have huu : (u : W.EE) * ↑u⁻¹ = 1 := u.mul_inv
  linear_combination (↑u⁻¹ : W.EE) * hy + x * huu

theorem mem_of_pow_smul_mem (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O)
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T) (m : ℕ) (x : W.DD T)
    (hx : ((PD.p : O) ^ m) • x ∈ W.N T) : x ∈ W.N T := by
  obtain ⟨b, hli, hsp⟩ := hb
  have hxs : x ∈ Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) := hsp ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hxs
  set a := b.repr ⟨_, hx⟩ with ha
  have h1 : ∑ j, algebraMap (LetA O n) W.EE (a j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hx⟩)
    rw [map_sum] at this
    simpa only [algebraMap_smul, map_smul, Submodule.subtype_apply] using this
  have h2 : ∑ j, ((PD.p : W.EE) ^ m * e j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    rw [← he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, ← algebraMap_smul W.EE ((PD.p : O) ^ m), map_pow, map_natCast]
  have h3 : ∀ j, algebraMap (LetA O n) W.EE (a j) = (PD.p : W.EE) ^ m * e j :=
    Fintype.linearIndependent_iffₛ.1 hli _ _ (h1.trans h2.symm)
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (ee_torsionFree W hp _ (by rw [← hy]; ring))
  have h4 : ∀ j, ∃ c : LetA O n, e j = algebraMap (LetA O n) W.EE c := by
    intro j
    obtain ⟨c, hc⟩ := W.EE_sat (a j) m (Ideal.mem_span_singleton'.2 ⟨e j, by rw [h3, mul_comm]⟩)
    refine ⟨c, sub_eq_zero.1 (hreg m _ ?_)⟩
    have := h3 j
    rw [hc, map_mul, map_pow, map_natCast] at this
    rw [mul_sub, this, sub_self]
  choose c hc using h4
  rw [← he]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hc, algebraMap_smul]
  exact (W.N T).smul_mem _ (b j).2

end Generic

end GlobalTheory.WachSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  first | exact @GlobalTheory.Models.SubModel.model_pre | exact GlobalTheory.Models.SubModel.model_pre | (intros; apply GlobalTheory.Models.SubModel.model_pre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVector
section
open PowerSeries GlobalTheory.BK

noncomputable section

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

theorem PhiMod.eq_xi_red_of_conn_eq_zero (P : PhiMod O K l e a ι) {v : Vec K a ι}
    (h : P.conn v = 0) : v = P.xi (red v) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [PhiMod.conn_xiExt] at h
  have hN : ∀ τ i, N K (w τ i) = 0 := fun τ i => by
    have := congrFun (congrFun (P.xiExt.injective (h.trans (map_zero _).symm)) τ) i
    simpa using this
  have hw : w = cst (red w) := by
    funext τ i
    ext n
    rcases n with _ | n
    · simp
    · have := congrArg (coeff (n + 1)) (hN τ i)
      rw [coeff_N, map_zero] at this
      have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hn)
  rw [PhiMod.xi_apply, PhiMod.red_xiExt, ← hw]

theorem PhiMod.mem_ext_of_plusInl (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) {B : Subalgebra O K⟦X⟧} {v : Vec K a ι}
    (h : (P.plusInl hy).app v ∈ (P.plus hy).ext B) : v ∈ P.ext B := by
  rw [PhiMod.plusInl_app] at h
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, hmv⟩ := (P.plus hy).mem_extc.1 (mem_tot.1 h τ)
  refine P.mem_extc.2 ⟨fun i => m (Sum.inl i), fun i => hm (Sum.inl i), ?_⟩
  have h0 : m (Sum.inr ()) = 0 := by
    have := congrFun hmv (Sum.inr ())
    simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this.symm
  funext i
  have := congrFun hmv (Sum.inl i)
  simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h0] using this

end GlobalTheory.BK

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

theorem exists_conn_eq_zeta_of_mem_Y (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Y) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  have hy' := mem_invE_of_mem_Y hy
  set P := D.toPhiMod.plus hy'
  set F := D.toPhiMod.plusInl hy'
  set G := D.toPhiMod.plusProj hy'
  set t := P.phi xVec - P.xi (red (P.phi xVec)) with ht
  have inj : ∀ v w, F.app v = F.app w → v = w := fun v w h => by
    rw [PhiMod.plusInl_app, PhiMod.plusInl_app] at h
    funext τ i
    exact congrFun (congrFun h τ) (Sum.inl i)
  have hct : P.conn t = F.app (D.zeta y) := by
    rw [ht, map_sub, PhiMod.conn_xi, sub_zero]
    exact D.conn_phi_extension_generator_eq_zeta hy'
  have hrt : red t = 0 := by
    rw [ht, map_sub, PhiMod.red_xi, sub_self]
  have hx : G.app t = 0 := by
    have h1 : (rankOne O K l e fun _ : ZMod a => 0).conn (G.app t) = 0 := by
      rw [← Hom.app_conn, hct, PhiMod.plusInl_app, PhiMod.plusProj_app]
      rfl
    rw [PhiMod.eq_xi_red_of_conn_eq_zero _ h1, Hom.red_app, hrt, map_zero, map_zero]
  have key : ∀ τ, t τ (Sum.inr ()) = 0 := fun τ => by
    have := congrFun (congrFun hx τ) ()
    rw [← join_eta t, PhiMod.plusProj_app] at this
    simpa using this
  set s : Vec K a ι := fun τ i => t τ (Sum.inl i)
  have hts : t = F.app s := by
    rw [PhiMod.plusInl_app]
    conv_lhs => rw [← join_eta t]
    congr 1
    funext τ
    exact key τ
  have hxM : (xVec : Vec K a (ι ⊕ Unit)) ∈ P.M := by
    rw [← PhiMod.bas_inr]
    exact P.bas_mem_M _
  have htM : t ∈ P.MMl := by
    refine sub_mem (P.ext_mono ((A_le_S l e).trans (le_away _ _)) (P.phi_mem_L hxM)) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a (ι ⊕ Unit) P).2 _).2 (mem_tot.2 fun τ i => ?_)
    rw [cst_apply]
    exact HasK.C_mem _
  refine ⟨s, D.toPhiMod.mem_ext_of_plusInl hy' (hts ▸ htM), fun g => ?_, inj _ _ ?_⟩
  · have hΔ : (D.desc.plus hy' hy.2).act g t = t := by
      rw [ht, map_sub, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g, Descent.act_xi,
        ← Descent.red_act, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g]
    apply inj
    have h2 : (D.desc.plus hy' hy.2).act g (F.app s) = F.app s := by rw [← hts]; exact hΔ
    exact ((Descent.plusInl D.desc hy' hy.2).app_act g s).trans h2
  · rw [Hom.app_conn, ← hts, hct]

end BKDat

end GlobalTheory.BK

namespace GlobalTheory.BK

namespace BKDat

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem exists_conn_eq_zeta (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Yl) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  obtain ⟨n, hn⟩ := D.desc.mem_Yl_iff.1 hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta_of_mem_Y hn
  have hl : ((l : K) ^ n) ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ n)⁻¹ • s, ?_, D.desc.inv.smul_mem _ hsi, ?_⟩
  · have : ((l : K) ^ n)⁻¹ • s = (fun _ : ZMod a => C ((l : K) ^ n)⁻¹) • s := by
      funext τ i
      simp [smul_eq_C_mul]
    rw [this]
    exact D.smul_tot_mem_ext (fun _ => HasK.C_mem _) hsM
  · rw [map_smul, hsc, map_smul, smul_smul, inv_mul_cancel₀ hl, one_smul]

theorem Mon_mem_range_Lc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Yl,
    (∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y ∧ ∃ d : D.D, (∀ g, D.desc.actD g d = d) ∧
      D.phi s - s - D.phi y = D.xi d) ∧ ∃ w ∈ D.Zl, D.Lc w = D.Mon y := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta hy
  have hyi : ∀ g, D.desc.act g y = y := hy.2
  have hsi' : ∀ g, D.desc.act g s = s := hsi
  refine ⟨⟨s, hsM, hsi, hsc, ?_⟩, D.cls (y - s), ⟨⟨y - s, ?_, rfl⟩, fun g => ?_⟩, ?_⟩
  · set v := D.phi s - s - D.phi y with hv
    have hcv : D.conn v = 0 := by
      have hz := D.zeta_eq y
      rw [PhiMod.lphi_apply, map_sub, smul_sub] at hz
      rw [hv, map_sub, map_sub, PhiMod.conn_phi, PhiMod.conn_phi, hsc, sub_right_comm]
      exact sub_eq_zero.2 hz.symm
    refine ⟨red v, fun g => ?_, D.eq_xi_red_of_conn_eq_zero hcv⟩
    rw [← Descent.red_act, hv]
    congr 1
    rw [(D.desc.act g).map_sub, (D.desc.act g).map_sub, Descent.act_phi, Descent.act_phi, hsi' g,
      hyi g]
  · rw [SetLike.mem_coe, mem_divE, smul_sub]
    refine sub_mem ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_A_le_Rpi l e) (mem_divE.1 hy.1)))
      ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_S_le_Rpi l e)
        (D.smul_mem_Mext ((A_le_S l e).trans (le_away _ _)) hsM)))
  · rw [Descent.actPol_cls, map_sub, hyi g, hsi' g]
  · rw [Lc_cls, PhiMod.Mon_apply, map_sub, PhiMod.EN_apply D.toPhiMod s, hsc]

end BKDat

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEndsStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_logConvex_in_radius : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  first | exact @GlobalTheory.PMon.Gauss.gC_logConvex | exact GlobalTheory.PMon.Gauss.gC_logConvex | (intros; apply GlobalTheory.PMon.Gauss.gC_logConvex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquivStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_H2_comp_equiv : ∀ {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (i : G ≃ₜ* Γ) (rho : Representation R Γ M), Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) := by
  first | exact @GlobalTheory.TransportH2.natCard_H2_comp | exact GlobalTheory.TransportH2.natCard_H2_comp | (intros; apply GlobalTheory.TransportH2.natCard_H2_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumberFieldPrimeZetaSumAddLogIsBigO
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.ChebCyc

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_add_log_sub_one_isBigO_one (K : Type) [Field K] [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) + Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hT := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hr : ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ ≠ 0 := by
    simp [dedekindZeta_residue_ne_zero]
  have hL := ((Real.continuousAt_log hr).tendsto.comp hT).isBigO_one ℝ
  refine hL.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  rw [norm_mul, _root_.GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp K hs]
  have hs1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hs1, Real.log_mul (sub_ne_zero.2 hs.ne') (Real.exp_pos _).ne', Real.log_exp]
  ring

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one (K : Type) [Field K]
    [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hN : ∀ P : HeightOneSpectrum (𝓞 K), 2 ≤ Ideal.absNorm P.asIdeal :=
    fun P => _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
  have hC := _root_.GlobalTheory.Mem.RayPrimes.logSum_sub_bounded (fun P : HeightOneSpectrum (𝓞 K) =>
    Ideal.absNorm P.asIdeal) hN (fun _ => 1) (fun _ => by simp)
    (fun s hs => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2)
  have hC' : (fun s : ℝ => (((∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hC.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
    congr 1
    · refine tsum_congr fun P => ?_
      rw [_root_.GlobalTheory.Mem.ZetaPole.ofReal_logFactor (by linarith [hN P]) (by linarith), one_mul]
    · refine tsum_congr fun P => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _), one_mul, Complex.ofReal_natCast,
        Complex.ofReal_neg]
  rw [← isBigO_norm_left]
  exact hC'.norm_left.congr_left fun s => Complex.norm_real _

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in

theorem _root_.GlobalTheory.ChebCyc.primeSum_add_log_isBigO : ∀ (K : Type) [Field K] [NumberField K], (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  intro K _ _
  refine ((tsum_logFactor_add_log_sub_one_isBigO_one K).sub
    (tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one K)).congr_left fun s => ?_
  ring

end GlobalTheory.ChebCyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFiniteStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ, DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | exact GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | (intros; apply GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnitStatement
section
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integral_unit_alt : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | exact GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | (intros; apply GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLe
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem senle_exists_coker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (C : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom B C q ∧ Function.Surjective q ∧ Function.Exact j q := by
  have hle : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (B.ρ g) := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A.ρ g x, hj g x⟩
  obtain ⟨C, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) hle)
  refine ⟨C, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => ?_,
    e.surjective.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    rfl
  · simp [Submodule.Quotient.mk_eq_zero]

theorem senle_exists_ker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (C : Ob k G) (s : (Fin C.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom C A s ∧ Function.Injective s ∧ Function.Exact s p := by
  have hle : ∀ g, LinearMap.ker p ≤ (LinearMap.ker p).comap (A.ρ g) := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker]
    rw [hp g x, hx, map_zero]
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) hle)
  refine ⟨C, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (Submodule.injective_subtype _).comp e.symm.injective, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, e.symm_apply_apply, e.symm_apply_apply]
    rfl
  · constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem sen_push_pre_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  intro k G _ _ l n _ _ _ R F B A₁ A j p w w' N hB hj hji hp hps hN i x
  have hA₁ : F.Obj A₁ := F.obj_sub A₁ B j hj hji hB
  obtain ⟨C, q, hq, hqs, hex⟩ := senle_exists_coker A₁ B j hj
  obtain ⟨K, s, hs, hsi, hex'⟩ := senle_exists_ker A₁ A p hp
  have h1 := GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B C j q N hB hj hq hji hqs hex i (hN.1 i) (hN.2.2 i) x
  have hsat := GlobalTheory.PhiGam.Sat.main R (F.D B) (F.D A₁) (F.map A₁ B j) (F.map_inj A₁ B j hA₁ hB hj hji)
    (F.map_φ A₁ B j hA₁ hB hj) (F.map_γ A₁ B j hA₁ hB hj) w w' N hN.1 hN.2.1 hN.2.2
  have h2 := GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ A s p (F.pre A₁ B j N) hA₁ hs hp hsi hps hex' i (hsat.1 i) (hsat.2.2 i) x
  omega

end GlobalTheory.Models
end

