import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.MonZero

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem galOB_mul (g h : GQ l) (r : OB l O) :
    galOB O (g * h) r = galOB O g (galOB O h r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul o w =>
    simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (fun z => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 g h w)

theorem actB_mul (T : LocLat (Gl l) ℚ_[l] K O) (g h : Gl l) (x : TW (OB l O) T) :
    actB (sQ l) T (g * h) x = actB (sQ l) T g (actB (sQ l) T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t =>
    have ht : T.actT (g * h) t = T.actT g (T.actT h t) :=
      Subtype.ext (show T.ρ (g * h) t = T.ρ g (T.ρ h t) by simp)
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, galOB_mul, ht]

theorem actB_one_tmul (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (t : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l O) ⊗ₜ[O] t) = (1 : OB l O) ⊗ₜ[O] T.actT g t := by
  simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem step_mul {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b) (g h k : Gl l)
    (hg : g = h * k) (hh : sQ l h ∈ GK (ϖ.field a)) (hk : sQ l k ∈ ϖ.GKinf) :
    ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  obtain ⟨xk, hxk⟩ := GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois l a e O K t ϖ ι η H D T R y hy b hb k hk
  obtain ⟨xh, hxh⟩ := GlobalTheory.T.potentialCocycle_mem_lPow_lattice l a e O K t ϖ ι η H D T R hηH hlH y hy c hc b hb h hh
    (GlobalTheory.T.galois_coboundary_mem_lattice_inv_l_of_monodromy_eq_zero hF l a e O K t ϖ hl2 ι η H D T R y hy hM b hb h hh)
  refine ⟨(l : O) ^ c • T.actT h xk + xh, ?_⟩
  have e1 : actB (sQ l) T g b - b = actB (sQ l) T h (actB (sQ l) T k b - b) + (actB (sQ l) T h b - b) := by
    rw [hg, actB_mul, map_sub]; abel
  rw [e1, hxk, actB_one_tmul, smul_add, hxh, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]

theorem cob_of (T : LocLat (Gl l) ℚ_[l] K O) (b : TW (OB l O) T) (c : ℕ) (X : Gl l → ↥T.L.T)
    (hX : ∀ g, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] X g) :
    IsCobOf (sQ l) T b (fun g => ((l : K) ^ c)⁻¹ • (X g : T.V)) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  intro g n x hx
  apply smul_cancel T c
  rw [smul_comm ((l : O) ^ c) ((l : O) ^ n), hX g, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [← algebraMap_smul K ((l : O) ^ c), ← algebraMap_smul K ((l : O) ^ n), map_pow, map_pow, map_natCast, hx,
    smul_comm ((l : K) ^ n), smul_smul ((l : K) ^ c), mul_inv_cancel₀ hne, one_smul]

theorem exists_cob {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b)
    (hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf) :
    ∃ κ : Gl l → T.V, IsCobOf (sQ l) T b κ ∧ ∀ g, (l : K) ^ c • κ g ∈ T.L.T := by
  have hX : ∀ g : Gl l, ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
    intro g
    obtain ⟨h, k, hg, hh, hk⟩ := hdec g
    exact step_mul t ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb g h k hg hh hk
  choose X hX using hX
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine ⟨_, cob_of T b c X hX, fun g => ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  exact (X g).2

end GlobalTheory.BKGal.MonZero

theorem GlobalTheory.BKGal.classOf_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  intro hF l _ a e _ _ ϖ LL _ _ ι _ _ η H D T R Pl AI hstd hηH hlH y hy hM c hc
  have hl2 : l ≠ 2 := by omega
  obtain ⟨b, hb⟩ := (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).1 y hy
  have hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf := by
    intro g
    obtain ⟨h, hh, k, hk, hgk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).1 (sQ l g)
    let hG : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
    refine ⟨hG, hG⁻¹ * g, (mul_inv_cancel_left hG g).symm, hh, ?_⟩
    have e1 : sQ l (hG⁻¹ * g) = k := by
      rw [map_mul, map_inv, show sQ l g = h * k from hgk]
      show h⁻¹ * (h * k) = k
      group
    rw [e1]; exact hk
  obtain ⟨κ, hcob, hT⟩ := GlobalTheory.BKGal.MonZero.exists_cob (thetaW a LL) ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb hdec
  have hcl : R.ClassOf y κ := ⟨b, hb, hcob⟩
  have hZ1c : κ ∈ continuousCocycles T.ρ := GlobalTheory.T.coboundary_mem_cocycles_odd_prime l hl2 LL T b κ hcob
  obtain ⟨β, -, -, -, hf⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hstd
  have hZ1f : κ ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := (hf κ hZ1c).2 ⟨b, hcob⟩
  refine ⟨(l : ↥LL.1) ^ c • κ, ?_, (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).2.2.1 y κ c hcl⟩
  refine ⟨⟨(continuousCocycles T.ρ).smul_mem _ hZ1c, ?_⟩, (finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ).smul_mem _ hZ1f⟩
  intro g _
  exact hT g
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassWachPairJumps
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineDescent

set_option maxHeartbeats 40000000 in
private theorem descend_element_of_le_of_eq_K0 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) (m : ℕ)
    (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) :
    ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m),
      ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  obtain ⟨y, hy, hjy⟩ := GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  exact ⟨y, hy, hjy⟩

set_option maxHeartbeats 60000000 in
private theorem descend_of_eq_K0_of_isCrys (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := by
  obtain ⟨y, hy, hjy⟩ := descend_element_of_le_of_eq_K0 D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  obtain ⟨z, hz, hjz⟩ := GlobalTheory.T.X_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT z' hz'
  obtain ⟨b', hb'⟩ := (GlobalTheory.WittTensorFixed.main l K' LL (resLt (K := K) (K' := K') (LL := LL) hle T)).1
    (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  obtain ⟨c', hc'cl, hc'0, hc'g⟩ := cl_fit D HW F K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) y' z' hyz' b' hb'
  obtain ⟨c, hcc', hZf⟩ := push_cocycle (D.locA l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop c'
  have hb : TWmap (φRW LL) T (toTW hle T b') - toTW hle T b' = ((F l).E K s LL h).tie.jD T y := by
    rw [toTW_φ, hb', hjy]
  have hone : ∀ g : ↥((HW l).W K s LL h).GKs,
      ((HW l).W K' s LL h').resΓ ((fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g : ↥((HW l).W K' s LL h').GKs) : ↥(GK K')) = 1 ↔
        ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g =>
    (resΓ_one_iff (D.loc l) K' LL _ ((HW l).W K' s LL h') _).trans
      (resΓ_one_iff (D.loc l) K LL _ ((HW l).W K s LL h) _).symm
  have hzero : ∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 →
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') g = 0 := by
    intro g hg
    rw [hZf b' g, hc'0 _ ((hone g).2 hg), toTW_zero]
  obtain ⟨lam', hlam'c, hlam'1, hlam'g, ⟨g', hg'⟩, -⟩ := lam_exists D HW K' s LL h'
  let lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l] := lam'.comp (fHom ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlamc : Continuous lam := hlam'c.comp (fMap_cont ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlam1 : ∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g hg =>
    (hone g).1 ((hlam'1 _).1 hg)
  have hfe : fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = g' := Subtype.ext (Subtype.ext rfl)
  have hg₁ : lam (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = Multiplicative.ofAdd 1 := by
    show lam' (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g')) = _
    rw [hfe, hg']
  have hZ₁ : Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') =
      ((F l).E K s LL h).tie.jD T z := by
    rw [hZf b' _, hfe, hc'g g' ((hlam'g g').1 hg'), hjz]
  have hall := GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline D HW F l K s LL h T hT c (toTW hle T b') lam hlamc hlam1 hzero _ hg₁ z hz hZ₁
  obtain ⟨lamK, -, -, hlamKg, ⟨g₀, hg₀⟩, -⟩ := lam_exists D HW K s LL h
  have hγ := (hlamKg g₀).1 hg₀
  obtain ⟨z₀, hz₀, hZ₀⟩ := hall g₀
  have hyz := GlobalTheory.T.herr_cocycle_of_witt_tensor_relations D HW F l K s LL h T c (toTW hle T b') y z₀ g₀ hγ hb hZ₀
  exact ⟨y, z₀, hyz, hy, hz₀, c, c',
    GlobalTheory.T.herr_class_of_cocycle_values D HW F l K s LL h T c (toTW hle T b') y z₀ hyz g₀ hγ hb hzero hZ₀, hc'cl, hcc'⟩

set_option maxHeartbeats 4000000 in

theorem descend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := descend_of_eq_K0_of_isCrys D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT m y' z' hyz' hy' hz'

set_option maxHeartbeats 60000000 in
private theorem wach_pow_smul_of_good_ext : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT M hh hJ κ hκ
  obtain ⟨K', h', hle, hK0, htop, hiff⟩ := base_setup D HW K s LL h
  have hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs :=
    fun g => (hiff _).2 g.2
  have hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K' := fun g => (hiff _).1 g.2
  have hT' := restrict_crys D hle T hT
  have hJ' := restrict_jumps D HW K s LL h K' h' hle T hT M hh hJ
    (fun τ' a hj => @GlobalTheory.T.hodgeTateJump_restrict_finite_ext l _ (D.loc l) (D.locA l) (D.locT l) K K' LL hle T.V _ _ _ _ _ T.ρ hT τ' a hj)
  obtain ⟨cκ, cκ', hcκ, hcκ'f, hcκ'⟩ := pull_h1f (D.loc l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm κ hκ
  obtain ⟨n, y', z', hyz', hy', hz', hcl'⟩ := GlobalTheory.T.H1f_class_of_wach_pair D HW F Cm l K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) hT' htop
    (fun _ => mx M) (fun _ => mx hh) hJ' _ hcκ'f
  haveI : Nonempty (Let K') := ⟨0⟩
  have hmx : mx (fun _ : Let K' => mx M) = mx M := ciSup_const
  rw [hmx] at hy'
  obtain ⟨y, z, hyz, hy, hz, c, c', hc, hc', hcc'⟩ :=
    descend D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT (mx M) y' z' hyz' hy' hz'
  exact ⟨n, y, z, hyz, hy, hz, hc.symm.trans ((push_class hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm hm' htop c cκ c' cκ' hcc' hcκ'
    _ (hc'.trans hcl')).trans (congrArg ((l ^ n : ℕ) • ·) hcκ))⟩

set_option maxHeartbeats 4000000 in

theorem pow_smul_from_complex : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := wach_pow_smul_of_good_ext

end GlobalTheory.NL.CrystallineDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrivOnRead

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infIdele_snd_one {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem fst_prod_apply {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K)
    (w : InfinitePlace K) : (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w :=
  map_prod ((Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) f s

theorem snd_prod {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem ideleMap_inf (w : InfinitePlace F) (k : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (infIdele F w (atInf w k)) = CharEx.aFi (L := E) F w k := by
  classical
  refine Units.ext (Prod.ext (funext fun w' => ?_) ?_)
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 w' = _
    rw [CharEx.aFi, Units.coe_prod, fst_prod_apply]
    change LiesOver.completionMap (v := w'.comap (algebraMap F E)) (w := w')
      ((infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 (w'.comap (algebraMap F E))) = _
    by_cases hw : w'.comap (algebraMap F E) = w
    · have hm : w' ∈ aboveInf (L := E) F w := by simp [aboveInf, hw]
      rw [Finset.prod_eq_single_of_mem w' hm (fun w'' _ h => infIdele_fst_ne E w'' w' (Ne.symm h) _),
        infIdele_fst_self]
      subst hw
      rw [infIdele_fst_self]
      exact LiesOver.completionMap_coe (v := w'.comap (algebraMap F E)) (w := w') (WithAbs.toAbs _ (k : F))
    · rw [infIdele_fst_ne F w _ hw, map_one]
      refine (Finset.prod_eq_one fun w'' hw'' => infIdele_fst_ne E w'' w' ?_ _).symm
      rintro rfl
      simp [aboveInf] at hw''
      exact hw hw''
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).2 = _
    rw [CharEx.aFi, Units.coe_prod, snd_prod]
    rw [Finset.prod_eq_one fun w'' _ => infIdele_snd_one w'' _]
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)

end General

open GlobalTheory.CharTransport in
set_option maxHeartbeats 800000 in

theorem exists_hom_tmul (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ a x, Θ (a ⊗ₜ[D.host.F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hΘ, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem trivOn_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  intro D c χ hc ha
  have hχ := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D c χ hc
  obtain ⟨Θ, hΘc, hΘt, hinc, hloc⟩ := exists_hom_tmul D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΘc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have hc' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, hloc P e he]
      rw [hcoe, this]
      rfl
  have hcc : c = c' := GlobalTheory.ChrEqUnique.idc_unique D c c' χ hc hc'
  have key : ∀ a : (AF D.host.F)ˣ, χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a) = 1 := fun a => by
    have h1 : u (idF D a) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a := Units.ext (by
      change Θ ((a : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
      rw [hΘt, map_one, mul_one]
      rfl)
    have h2 := hcoe (idF D a)
    rw [← hcc, ha, h1] at h2
    exact Units.ext (by rw [← h2]; rfl)
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · rw [CharEx.resFin_eq]
    change χ.1 (GlobalTheory.Mem.Chr.locF D.host.F v k) = 1
    rw [← GlobalTheory.ToricDistribution.ideleMap_local]
    exact key _
  · rw [CharEx.resInf_eq, ← ideleMap_inf]
    exact key _

end GlobalTheory.TrivOnRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SumProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

theorem sum_fst_of_lFactors {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL k} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors hx).symm.trans hd

theorem exists_isLSeg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π)
    {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : ∃ y : IrrGL k, IsLSeg Δ y.rep := by
  obtain ⟨_, x, -, ⟨D, ⟨rfl, -⟩, hD⟩, -⟩ := h
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hΔ
  exact ⟨x a, hD a⟩

theorem exists_isL [CharZero k] (hS : StandardCosocleGL) {𝔪 : Multiset (Segment k)}
    (h : ∀ Δ ∈ 𝔪, ∃ y : IrrGL k, IsLSeg Δ y.rep) (hN : (𝔪.map Segment.deg).sum = N) :
    ∃ π : IrrRep (GL (Fin N) k), IsL 𝔪 π.ρ := by
  obtain ⟨D, hD⟩ := exists_isOrderedForm 𝔪
  have hm : ∀ i, D i ∈ 𝔪 := fun i => hD.1 ▸ Multiset.mem_map_of_mem D (Finset.mem_univ i)
  choose x hx using fun i => h _ (hm i)
  have hF : LFactors 𝔪 x := ⟨D, hD, hx⟩
  have hd : ∑ a, (x a).1 = N := (sum_fst_of_lFactors hF).trans hN
  obtain ⟨π, hπ⟩ := hS k 𝔪 _ _ x hd hF
  exact ⟨π, _, x, hd, hF, hπ⟩

theorem isL_add_of_equiv_prod₂ : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  rintro hM hS k _ _ _ _ _ r t σ τ π 𝔪 𝔫 h1 h2 ⟨e⟩
  obtain ⟨y, hy⟩ := exists_isL (N := r + t) hS (𝔪 := 𝔪 + 𝔫)
    (fun Δ hΔ => (Multiset.mem_add.1 hΔ).elim (exists_isLSeg_of_isL h1) (exists_isLSeg_of_isL h2))
    (by rw [Multiset.map_add, Multiset.sum_add, deg_of_isL h1, deg_of_isL h2])
  have hd : ∑ a, (![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ.ρ σ.smooth σ.irr τ.ρ τ.smooth τ.irr hd
  have ψ := IrrGL.equivOf y.ρ y.smooth y.irr
  have a1 : IsL 𝔪 (IrrGL.of σ.ρ σ.smooth σ.irr).rep := h1.of_equiv (IrrGL.equivOf _ _ _)
  have a2 : IsL 𝔫 (IrrGL.of τ.ρ τ.smooth τ.irr).rep := h2.of_equiv (IrrGL.equivOf _ _ _)
  have a3 : IsL (𝔪 + 𝔫) (IrrGL.of y.ρ y.smooth y.irr).rep := hy.of_equiv ψ
  have hs := (hM k).2 𝔪 𝔫 ![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr]
    (IrrGL.of y.ρ y.smooth y.irr) hd a1 a2 a3
  have E := (e.trans φ).symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)) (IrrRep.irr _) π.irr
  exact a3.of_equiv θ.symm

end GlobalTheory.LocGL.SumProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegmentStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsClassification_twist_multisegment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  first | exact @GlobalTheory.LocGL.isL_map_tw_of_isL | exact GlobalTheory.LocGL.isL_map_tw_of_isL | (intros; apply GlobalTheory.LocGL.isL_map_tw_of_isL <;> assumption)
end

