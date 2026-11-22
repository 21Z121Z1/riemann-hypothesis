import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0415
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPointIntegralRelativeLocalBasis
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

open Matrix

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_natCast_eq_one (l : ℕ) [Fact l.Prime] {s : ℕ} (hs : ¬ l ∣ s) : ‖(s : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs)

theorem norm_le_one_of_cols {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ} (U : Matrix (Fin n) (Fin n) C) (p : C)
    (hp : ‖p‖ < 1) (h : ∀ b, ∃ T : Fin n → C, (∀ c, ‖T c‖ ≤ 1) ∧ ∀ a, ‖U a b - p * ∑ c, U a c * T c‖ ≤ 1) (a b : Fin n) :
    ‖U a b‖ ≤ 1 := by
  haveI : Nonempty (Fin n × Fin n) := ⟨(a, b)⟩
  obtain ⟨⟨a₀, b₀⟩, hmax⟩ := Finite.exists_max fun q : Fin n × Fin n => ‖U q.1 q.2‖
  refine (hmax (a, b)).trans ?_
  obtain ⟨T, hT, hU⟩ := h b₀
  by_contra hm
  have hm : 1 < ‖U a₀ b₀‖ := not_le.1 hm
  have h1 : ‖∑ c, U a₀ c * T c‖ ≤ ‖U a₀ b₀‖ :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hT c)).trans (hmax (a₀, c))
  have h2 : ‖p * ∑ c, U a₀ c * T c‖ < ‖U a₀ b₀‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_lt (mul_lt_of_lt_one_left (one_pos.trans hm) hp)
  have h3 := IsUltrametricDist.norm_add_le_max (U a₀ b₀ - p * ∑ c, U a₀ c * T c) (p * ∑ c, U a₀ c * T c)
  rw [sub_add_cancel] at h3
  exact absurd h3 (not_le.2 (max_lt ((hU a₀).trans_lt hm) h2))

theorem exists_col {A E : Type} [CommRing A] [CommRing E] (j : E →+* A) (S : Subring A) {n : ℕ}
    (happ : ∀ M : ℕ, 0 < M → ∀ z : A, ∃ (e : E) (s : A), s ∈ S ∧ z = j e + (M : A) * s)
    (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Yi * Y = 1) {N : ℕ} (hN : 0 < N) (hNm : ∀ a b, (N : A) * Yi a b ∈ S)
    {p : ℕ} (hp : 0 < p) (b : Fin n) :
    ∃ (x : Fin n → E) (t : Fin n → A), (∀ c, t c ∈ S) ∧ Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t := by
  choose x s hs hx using fun i => happ (p * N) (Nat.mul_pos hp hN) (Y i b)
  refine ⟨x, ((N : A) • Yi) *ᵥ s, fun c => ?_, ?_⟩
  · rw [Matrix.mulVec, dotProduct]
    exact S.sum_mem fun k _ => S.mul_mem (hNm c k) (hs k)
  · have e : (fun i => j (x i)) = Y *ᵥ Pi.single b 1 - (p : A) • (N : A) • s := by
      funext i
      rw [Matrix.mulVec_single_one]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
      rw [hx i]
      push_cast
      ring
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.smul_mulVec]

theorem read_col {A E C : Type} [CommRing A] [CommRing E] [CommRing C] (j : E →+* A) (ev : A →+* C) (inc : E →+* C)
    (hj : ∀ e, ev (j e) = inc e) {n : ℕ} (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Y * Yi = 1) (Bi : Matrix (Fin n) (Fin n) E)
    {p : ℕ} {b : Fin n} {x : Fin n → E} {t : Fin n → A}
    (h : Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t) (a : Fin n) :
    (Bi.map inc * Y.map ev) a b - (p : C) * ∑ c, (Bi.map inc * Y.map ev) a c * ev (t c) = inc ((Bi *ᵥ x) a) := by
  have h1 : Y *ᵥ (Pi.single b 1 - (p : A) • t) = fun i => j (x i) := by
    rw [← h, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec]
  have h2 : (ev ∘ (Pi.single b 1 - (p : A) • t : Fin n → A)) = Pi.single b 1 - (p : C) • fun c => ev (t c) := by
    funext c
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_natCast,
      Pi.single_apply, apply_ite ev, map_one, map_zero]
  have h3 : Y.map ev *ᵥ (Pi.single b 1 - (p : C) • fun c => ev (t c)) = inc ∘ x := by
    funext i
    rw [← h2, ← RingHom.map_mulVec, h1, hj]
    rfl
  rw [RingHom.map_mulVec, ← h3, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

theorem stdLat_of {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (h : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Seed.FrmC.StdLat V := by
  intro x
  show (∑ i, x i • V.frame i ∈ V.L0) ↔ _
  rw [h, V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), V.frame.repr_sum_self]
  exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem approx (M : ℕ) (hM : 0 < M) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ (e : E) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F), s ∈ Formalism.L2.Herm.intAf F E ∧
      z = e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) + (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨e₁, s₁, h₁, rfl⟩ := hx
    obtain ⟨e₂, s₂, h₂, rfl⟩ := hy
    refine ⟨e₁ + e₂, s₁ + s₂, add_mem h₁ h₂, ?_⟩
    rw [TensorProduct.add_tmul]
    ring
  | tmul b α =>
    obtain ⟨d, hd, ho⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E b
    obtain ⟨x, β, hβ, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F (M * d) (Nat.mul_pos hM hd) α
    refine ⟨x • b, ((d : E) * b) ⊗ₜ[F] β, GlobalTheory.PlaceDatum.tmul_mem_int ho (α := β) hβ, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      ← nsmul_eq_mul, ← nsmul_eq_mul, mul_smul]
    rfl

theorem norm_ev_le_one {l : ℕ} [Fact l.Prime] {inc : E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (hev : EvOk inc ev) {r : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hr : r ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm r)‖ ≤ 1 := by
  induction hr using Subring.closure_induction with
  | mem r hr =>
    rcases hr with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
    · refine (congrArg norm (hev.1 (algebraMap (𝓞 E) E o))).le.trans ?_
      exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
    · exact hev.2.1 β hβ
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

end General

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem norm_le_one_of_isLocBasis : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val a b‖ ≤ 1 := by
  intro D V l hl inc ev hev hL0 y B hB
  have hV := stdLat_of V hL0
  have hY := GlobalTheory.HLatStd.invM_mul y
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (GlobalTheory.HLatStd.invM y)
  let j : D.host.E →+* Lev.EAf D := Algebra.TensorProduct.includeLeftRingHom
  let ev' : Lev.EAf D →+* PadicAlgCl l := ev.comp (GlobalTheory.HeckeTrans.unswap D)
  have hU : ((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val =
      (B⁻¹).val.map inc * ((Units.val ((y : Bridge.Gf V) : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).map (Lev.swapAE D)).map ev' := by
    rw [← map_inv, Units.val_mul]
    congr 1
    ext a b
    exact (congrArg ev (GlobalTheory.HeckeTrans.unswap_swap _)).symm
  rw [hU]
  refine norm_le_one_of_cols _ (l : PadicAlgCl l) (norm_natCast_lt_one l) fun b => ?_
  obtain ⟨x, t, ht, hx⟩ := exists_col j (GlobalTheory.StdFrameExist.SI D) (fun M hM z => approx M hM z) _ _
    (mul_eq_one_comm.1 hY) hN hNm hl.out.pos b
  refine ⟨fun c => ev' (t c), fun c => norm_ev_le_one hev (ht c), fun a => ?_⟩
  rw [read_col j ev' inc (fun e => hev.1 e) _ _ hY _ hx a]
  have hmem : x ∈ Bridge.hLat V y := by
    refine GlobalTheory.HLatStd.mem_hLat_of hV y fun i => ?_
    have hi : (GlobalTheory.HLatStd.invM y *ᵥ GlobalTheory.HLatStd.iv x) i = _ := congrFun hx i
    rw [hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    refine sub_mem ?_ (mul_mem (natCast_mem _ _) (ht i))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨s, hs, hint⟩ := (hB x).1 ⟨1, hl.out.not_dvd_one, by rw [Nat.cast_one, one_smul]; exact hmem⟩
  obtain ⟨o, ho⟩ := hint a
  have h1 : ‖inc (algebraMap (𝓞 D.host.E) D.host.E o)‖ ≤ 1 :=
    GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
  rwa [ho, map_mul, map_natCast, norm_mul, norm_natCast_eq_one l hs, one_mul] at h1

end GlobalTheory.LocBasisInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

theorem GlobalTheory.BigTop.Fun.arch_tie (hS : SetAt)
    (hd : Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (_hA : GlobalTheory.NormSum.ArchSt) (_hB : BotSmall) : Arch @Comparison₂ := by
  have hQ := GlobalTheory.T.fitted_ties_bound_eventual _ hS hd GlobalTheory.T.archimedeanBound_bottomPairs_norms_grid
  refine Lf.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  have hA := hq d.zA d.zA' hsq.norms
  show ArchimedeanHeightBound d.zA d.zA' (d.O.bArch C p.Z.b)
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  have e1 : d.O.bArch C p.Z.b = C * D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        (Real.log p.Z.b + Real.log ((GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)))) +
      C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 *
        (Real.log p.Z.b + Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ))) +
      C * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    unfold FunData.bArch
    rw [eN, eB, eS, ef]
  rw [e1]
  exact hA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementMovesCoefficientLatticeByPrimePowStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow : CentLat := by
  first | exact @GlobalTheory.CentralLattice.centLat | exact GlobalTheory.CentralLattice.centLat | (intros; apply GlobalTheory.CentralLattice.centLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtSmallPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_small_place : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  first | exact @GlobalTheory.LevelCharExp.chiAt_inRange | exact GlobalTheory.LevelCharExp.chiAt_inRange | (intros; apply GlobalTheory.LevelCharExp.chiAt_inRange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSums_span_cuspForms_baseTuple_second_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) := by
  first | exact @GlobalTheory.ClassSumSpanCore.classSumsSpan_core | exact GlobalTheory.ClassSumSpanCore.classSumsSpan_core | (intros; apply GlobalTheory.ClassSumSpanCore.classSumsSpan_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

section GenericCmp

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L,
    d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  set v := Module.finBasis (FractionRing O) M
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← v.sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_eq_smul_of_read
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (s t : L ⊗[O] M) (a : ℂ) (h : readExt rd eL hL s = a • readExt rd eL hL t) (h0 : readExt rd eL hL s ≠ 0) :
    ∃ b : L, eL b = a ∧ s = b • t := by
  set R := readExt rd eL hL with hR
  set v := Module.finBasis (FractionRing O) M
  have hne : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsm : ∀ (d : O) (x : L ⊗[O] M), R (d • x) = eL (algebraMap O L d) • R x := fun d x => by
    rw [← algebraMap_smul L d x, hR, readExt_smul]
  have hsum : ∀ c : _ → L, R (∑ k, c k ⊗ₜ v k) = ∑ k, eL (c k) • rd (v k) := fun c => by
    rw [map_sum]
    rfl
  obtain ⟨d, hd, c, es⟩ := exists_smul_eq_sum_finBasis s
  obtain ⟨d', hd', c', et⟩ := exists_smul_eq_sum_finBasis t
  have hcoef : ∀ k, eL (algebraMap O L d') * eL (c k) = a * (eL (algebraMap O L d) * eL (c' k)) := fun k => by
    have e1 : ∑ k, (eL (algebraMap O L d') * eL (c k) - a * (eL (algebraMap O L d) * eL (c' k))) • rd (v k) = 0 := by
      have h1 : eL (algebraMap O L d') • R (d • s) = a • eL (algebraMap O L d) • R (d' • t) := by
        rw [hsm, hsm, h]
        simp only [smul_smul]
        congr 1
        ring
      rw [es, et, hsum, hsum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [h1, sub_self]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ e1 k)
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    have h2 : eL (algebraMap O L d) • R s = 0 := by
      rw [← hsm, es, hsum]
      simp [hc]
    exact (smul_eq_zero.1 h2).resolve_left (hne d hd)
  have hl : eL (algebraMap O L d') * eL (c k) ≠ 0 := mul_ne_zero (hne d' hd') ((map_ne_zero eL).2 hk)
  have hr : eL (algebraMap O L d) * eL (c' k) ≠ 0 := fun h3 => hl (by rw [hcoef k, h3, mul_zero])
  refine ⟨(algebraMap O L d' * c k) / (algebraMap O L d * c' k), ?_, ?_⟩
  · rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
  · have hb : eL ((algebraMap O L d' * c k) / (algebraMap O L d * c' k)) = a := by
      rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
    apply readExt_injective rd eL hL hF
    rw [readExt_smul, hb, ← hR, h]

end GenericCmp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.SerBase

set_option maxHeartbeats 4000000 in

theorem readCmpAt : ReadCmpAt := by
  unfold ReadCmpAt
  refine AtTw.of_forall fun Fm x hx i p hr hm w _ j => ?_
  intro ρ hρ e he1 he2 ν hν rd hcan u hu f y a hfa
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add, map_add]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have htop : ∀ y, y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)) := fun y => by
    obtain ⟨n, b, hmem, -, -, -, hLs⟩ := hK
    have h2 : (p.nexp.fi j).e.symm y ∈ Submodule.span (Fm.D x i).what₂.LL (Set.range b) := hLs ▸ Submodule.mem_top
    have h3 := Submodule.mem_map_of_mem (f := (p.nexp.fi j).e.toLinearMap) h2
    rw [Submodule.map_span] at h3
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨b k, hmem k, rfl⟩
  have hv : (fun τ => (u τ : ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)).sm τ)) = p.v₀ j (sg0 (Fm.D x i) p.P.A3.A) := funext hu
  have h1 : R ((1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ f) = a • R (rd y) := by
    rw [hRdef, readExt_tmul, map_one, one_smul, hfa, ← hRdef, hrd y (htop y), hv]
  by_cases hf : f = 0
  · exact Or.inl hf
  · refine Or.inr (readExt_eq_smul_of_read _ e hL hF _ _ a h1 ?_)
    rw [readExt_tmul, map_one, one_smul]
    exact fun h0 => hf (hF.injective (h0.trans (map_zero _).symm))

end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharactersEmbeddingsOfCharacterisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A))) := by
  first | exact @GlobalTheory.GalLift.conjChars_five | exact GlobalTheory.GalLift.conjChars_five | (intros; apply GlobalTheory.GalLift.conjChars_five <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentationStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_cuspForms_finite_regularRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  first | exact @GlobalTheory.ShareOn.Definite.share_definite | exact GlobalTheory.ShareOn.Definite.share_definite | (intros; apply GlobalTheory.ShareOn.Definite.share_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnityStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {cR : Bridge.CoefDat D D.sp.X'} {cL : ∀ i : Fin m, Bridge.CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, Bridge.LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, Bridge.LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : Bridge.FamReal D A cR cL lR lL) (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ i : Fin m, D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR gramR' : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R c0R' : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L c0L' : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W),
    Bridge.FamTie B pl S Qt tauL lamR lamL gramR c0R c0L → Bridge.FamTie B pl S Qt tauL lamR lamL gramR' c0R' c0L' →
    ∀ i : Fin m, ∃ a : D.what₂.LL, (∃ k : ℕ, k ≠ 0 ∧ a ^ k = 1) ∧ ∀ F, c0L' i F = D.what₂.embLL a • c0L i F := by
  first | exact @GlobalTheory.CoefRoot.coef_root | exact GlobalTheory.CoefRoot.coef_root | (intros; apply GlobalTheory.CoefRoot.coef_root <;> assumption)
end
end

