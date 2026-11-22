import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProjectionToLevi
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.LeviProj

theorem exists_proj_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (P N M A : Subgroup G) (cP : IsClosed (P : Set G))
    (cN : IsClosed (N : Set G)) (cM : IsClosed (M : Set G)) (cA : IsClosed (A : Set G)) (hN : N ≤ P) (hM : M ≤ P)
    (hA : A ≤ P) (norm : ∀ p ∈ P, ∀ u ∈ N, p * u * p⁻¹ ∈ N) (comm : ∀ m ∈ M, ∀ t ∈ A, m * t = t * m)
    (inj : ∀ m ∈ M, ∀ t ∈ A, m * t ∈ N → m = 1 ∧ t = 1)
    (surj : ∀ p ∈ P, ∃ u ∈ N, ∃ m ∈ M, ∃ t ∈ A, p = u * m * t) :
    ∃ μ : G → G, ContinuousOn μ (P : Set G) ∧ (∀ p ∈ P, μ p ∈ M) ∧ (∀ p ∈ P, ∀ q ∈ P, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ N, ∀ m ∈ M, ∀ t ∈ A, μ (u * m * t) = m := by
  classical
  haveI : LocallyCompactSpace P := cP.locallyCompactSpace
  haveI : LocallyCompactSpace M := cM.locallyCompactSpace
  haveI : LocallyCompactSpace A := cA.locallyCompactSpace
  let N' : Subgroup P := N.subgroupOf P
  haveI : N'.Normal := ⟨fun u hu p => norm p p.2 u hu⟩
  haveI : IsClosed (N' : Set P) := cN.preimage continuous_subtype_val
  let ψ : M × A →* P := (Subgroup.inclusion hM).noncommCoprod (Subgroup.inclusion hA)
    fun m t => Subtype.ext (comm m m.2 t t.2)
  have hψ : ∀ z : M × A, (ψ z : G) = z.1 * z.2 := fun z => rfl
  let φ : M × A →* P ⧸ N' := (QuotientGroup.mk' N').comp ψ
  have cφ : Continuous φ := by
    refine QuotientGroup.continuous_mk.comp (Continuous.subtype_mk ?_ _)
    change Continuous fun z : M × A => (z.1 : G) * z.2
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have key : ∀ u ∈ N, ∀ (m : M) (t : A) (h : u * m * t ∈ P), φ (m, t) = (⟨_, h⟩ : P) := fun u hu m t h => by
    refine QuotientGroup.eq.2 ?_
    change ((m : G) * t)⁻¹ * (u * m * t) ∈ N
    have := norm _ (P.inv_mem (P.mul_mem (hM m.2) (hA t.2))) u hu
    rwa [inv_inv, mul_assoc, ← mul_assoc u] at this
  have sφ : Function.Surjective φ := fun q => by
    obtain ⟨⟨p, hp⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, m, hm, t, ht, rfl⟩ := surj p hp
    exact ⟨_, key u hu ⟨m, hm⟩ ⟨t, ht⟩ hp⟩
  have iφ : Function.Injective φ := (injective_iff_map_eq_one φ).2 fun z hz => by
    have := inj z.1 z.1.2 z.2 z.2.2 ((QuotientGroup.eq_one_iff (N := N') (ψ z)).1 hz)
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  let e := MulEquiv.ofBijective φ ⟨iφ, sφ⟩
  have ce : Continuous e.symm :=
    (e.toEquiv.toHomeomorphOfContinuousOpen cφ (φ.isOpenMap_of_sigmaCompact sφ cφ)).symm.continuous
  refine ⟨fun g => if h : g ∈ P then (e.symm (⟨g, h⟩ : P)).1 else 1, ?_, fun p hp => ?_, fun p hp q hq => ?_,
    fun u hu m hm t ht => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : Continuous fun p : P => ((e.symm p).1 : G) :=
      continuous_subtype_val.comp (continuous_fst.comp (ce.comp QuotientGroup.continuous_mk))
    exact this.congr fun p => by simp
  · simp only [dif_pos hp, SetLike.coe_mem]
  · simp only [dif_pos hp, dif_pos hq, dif_pos (P.mul_mem hp hq)]
    rw [← Subgroup.coe_mul, ← Prod.fst_mul, ← map_mul]
    rfl
  · have h : u * m * t ∈ P := P.mul_mem (P.mul_mem (hN hu) (hM hm)) (hA ht)
    simp only [dif_pos h]
    rw [e.symm_apply_eq.2 (key u hu ⟨m, hm⟩ ⟨t, ht⟩ h).symm]

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}

theorem conj_scalar {p g : UJ ε} {U' : Submodule ℂ (Fin n → ℂ)} {c : ℂ} {y : Fin n → ℂ}
    (hp : ∀ y ∈ U', uMat p *ᵥ y ∈ U') (h : uMat g *ᵥ (uMat p⁻¹ *ᵥ y) - c • (uMat p⁻¹ *ᵥ y) ∈ U') :
    uMat (p * g * p⁻¹) *ᵥ y - c • y ∈ U' := by
  have := hp _ h
  rwa [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv,
    one_mulVec] at this

theorem keeps_orth {p : UJ ε} {U : Submodule ℂ (Fin n → ℂ)} (hp : ∀ y ∈ U, uMat p *ᵥ y ∈ U) {y : Fin n → ℂ}
    (hy : ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ y) = 0) : ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ (uMat p⁻¹ *ᵥ y)) = 0 := fun z hz => by
  have e := conjTranspose_inv_mul_Jm p⁻¹
  rw [inv_inv] at e
  rw [mulVec_mulVec, ← e, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  exact hy _ (hp z hz)

theorem conj_mem_flagN {p u : UJ ε} (hp : p ∈ parab ε W) (hu : u ∈ flagN ε W) : p * u * p⁻¹ ∈ flagN ε W := by
  have hq := (parab ε W).inv_mem hp
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · simpa using conj_scalar (c := 1) (hp _) (by simpa using hu.1 i _ (hq _ y hy))
  · simpa using conj_scalar (c := 1) (hp _) (by simpa using hu.2 _ (keeps_orth (hp _) hy))

theorem comm_of_isSplit (hW : IsIsoFlag ε j W) {l t : UJ ε} {x : Fin a → ℝ} (hl : l ∈ flagM ε W)
    (ht : IsSplit ε W x t) : l * t = t * l := by
  have hp : l ∈ parab ε W := fun i y hy => (hl i y hy).1
  have hq := (parab ε W).inv_mem hp
  have : IsSplit ε W x (l * t * l⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hl ht.1) ((leviSub ε W).inv_mem hl), fun i y hy => ?_,
      fun y hy => ?_⟩
    · exact conj_scalar (hp _) (ht.2.1 i _ (hq _ y hy))
    · simpa using conj_scalar (c := 1) (hp _) (by simpa using ht.2.2 _ (keeps_orth (hp _) hy))
  exact mul_inv_eq_iff_eq_mul.1 ((existsUnique_isSplit hW x).unique this ht)

theorem exists_leviOne_part : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    (∀ i, 1 ≤ j i) →
    ∃ μ : UJ ε → UJ ε, ContinuousOn μ (parab ε W : Set (UJ ε)) ∧ (∀ p ∈ parab ε W, μ p ∈ leviOne ε W) ∧
      (∀ p ∈ parab ε W, ∀ q ∈ parab ε W, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ (x : Fin a → ℝ) (t : UJ ε), IsSplit ε W x t →
        u * m * t ∈ parab ε W ∧ μ (u * m * t) = m := by
  intro n a ε j W hW hj
  obtain ⟨⟨N, eN⟩, cN, kN⟩ := UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  have mN : ∀ {u}, u ∈ N ↔ u ∈ flagN ε W := fun {u} => by rw [← eN]; rfl
  obtain ⟨h, hc, h1, -, hh⟩ := exists_height hW hj
  have hx : ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → h (m * t) = x := fun m hm x t ht => by
    simpa [h1] using hh 1 (mN.1 N.one_mem) m hm x t ht 1
  let A : Subgroup (UJ ε) :=
    { carrier := {t | ∃ x, IsSplit ε W x t}
      one_mem' := ⟨0, isSplit_one⟩
      mul_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.mul h'⟩
      inv_mem' := fun {t} ⟨x, h⟩ => by
        obtain ⟨t', h', -⟩ := existsUnique_isSplit hW (-x)
        have := h.mul h'
        rw [add_neg_cancel] at this
        exact ⟨_, inv_eq_of_mul_eq_one_right ((existsUnique_isSplit hW 0).unique this isSplit_one) ▸ h'⟩ }
  have cA : IsClosed (A : Set (UJ ε)) := by
    have : (A : Set (UJ ε)) = {t | IsSplit ε W (h t) t} := by
      ext t
      refine ⟨fun ⟨x, ht⟩ => ?_, fun ht => ⟨_, ht⟩⟩
      have := hx 1 (one_mem _) x t ht
      rw [one_mul] at this
      rwa [Set.mem_ofPred_eq, this]
    rw [this]
    simp only [IsSplit, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_flagM W).inter (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ =>
        (W _).closed_of_finiteDimensional.preimage
          ((continuous_uMat.matrix_mulVec continuous_const).sub (by fun_prop))
    · exact isClosed_iInter fun y => isClosed_iInter fun _ =>
        (W _).closed_of_finiteDimensional.preimage
          ((continuous_uMat.matrix_mulVec continuous_const).sub continuous_const)
  have hN : N ≤ parab ε W := fun u hu => kN u (mN.1 hu)
  have hM : leviOne ε W ≤ parab ε W := fun m hm i y hy => (hm.1 i y hy).1
  have hA : A ≤ parab ε W := fun t ⟨_, ht⟩ i y hy => (ht.1 i y hy).1
  obtain ⟨μ, c, m1, m2, m3⟩ := exists_proj_of_closed (parab ε W) N (leviOne ε W) A isClosed_parab (eN ▸ cN)
    (isClosed_leviOne hW hj) cA hN hM hA (fun p hp u hu => mN.2 (conj_mem_flagN hp (mN.1 hu)))
    (fun m hm t ⟨_, ht⟩ => comm_of_isSplit hW hm.1 ht)
    (fun m hm t ⟨x, ht⟩ hu => by
      have e : m * t = 1 := GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW _ (mN.1 hu) _
        ((leviSub ε W).inv_mem ((leviSub ε W).mul_mem hm.1 ht.1))
        (by rw [mul_inv_cancel]; exact (compactSub ε).one_mem)
      have := hx m hm x t ht
      rw [e, h1] at this
      have e' : t = 1 := (existsUnique_isSplit hW x).unique ht (this ▸ isSplit_one)
      exact ⟨by simpa [e'] using e, e'⟩)
    (fun p hp => by
      obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
      exact ⟨u, mN.2 hu, m, hm, t, ⟨x, ht⟩, rfl⟩)
  exact ⟨μ, c, m1, m2, fun u hu m hm x t ht => ⟨mul_mem (mul_mem (hN (mN.2 hu)) (hM hm)) (hA ⟨x, ht⟩),
    m3 u (mN.2 hu) m hm t ⟨x, ht⟩⟩⟩

end GlobalTheory.LeviProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosAtBase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PosAtBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Wp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) (i : Fin D.R.m) :
    R.Wp3 i p = R.Wc' i c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ ((hU p c c0 hc h0).2 i).le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.Wc' i c) c0 h0 le_rfl

theorem EEp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) :
    R.EEp3 p = R.EEc c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ (hU p c c0 hc h0).1.le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.EEc c) c0 h0 le_rfl

theorem Wp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) (i : Fin D.R.m) :
    R.Wp3 i p = ⊥ := by
  unfold RealDat3.Wp3
  simp [h]

theorem EEp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) :
    R.EEp3 p = ⊥ := by
  unfold RealDat3.EEp3
  simp [h]

example (R : RealDat3 D A3 Ks) c : R.EEc c = GlobalTheory.Hk3.EEc R.toRealDat R.SF c := rfl

end GlobalTheory.PosAtBase

namespace GlobalTheory.PosAtBase

set_option maxHeartbeats 1000000 in

theorem pos_at_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (_hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (_hE : R.toRealDat.ExAt)
    (hS : Scal R.toRealDat R.SF) (hM : MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    (hex : ∃ p, R.EEp3 p ≠ ⊥) :
    0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
  obtain ⟨lam, κ, hκ, hl, hA, hB⟩ := hS
  have hlam : ∀ i t p c, R.Carries p c → R.Wc' i c ≠ ⊥ → R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i t p c hc hne
    have hW := Wp3_eq hU hc i
    refine hC.scal.lam0 i t p _ (by rw [hW]; exact hne) fun x hx ↦ hA i t c x ?_
    rw [hW] at hx
    exact hx
  have hpos : ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
    intro i t p
    by_cases hW : R.Wp3 i p = ⊥
    · rw [hC.scal.abs0 i t p hW]
      exact Real.exp_pos _
    · by_cases hc : ∃ c, R.Carries p c
      · obtain ⟨c, hc⟩ := hc
        rw [hlam i t p c hc (by rw [← Wp3_eq hU hc i]; exact hW)]
        exact hl i t c
      · exact absurd (Wp3_bot (not_exists.1 hc) i) hW
  refine ⟨?_, hpos⟩
  have hK : Lift.IsKap D.R.m (fun t ↦ R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    by_cases hc : ∃ c, R.Carries p c
    · obtain ⟨c, hc⟩ := hc
      have hx' : x ∈ R.EEc c := EEp3_eq hU hc ▸ hx
      have hpr : ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j, lam j t c :=
        (RealDat3.prod_lamN t p).trans (Finset.prod_congr rfl fun j _ ↦ hlam j t p c hc (hM c hc.1 j))
      have h1 := hB t c x hx'
      calc (R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) x = R.Th t (LinearMap.adjoint (R.Th t) x) := rfl
        _ = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x := h1
        _ = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by rw [hpr]
    · have hb : R.EEp3 p = ⊥ := EEp3_bot (not_exists.1 hc)
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).1 (hb ▸ hx)
      subst hx0
      rw [map_zero, smul_zero]
  obtain ⟨p, hp⟩ := hex
  rw [hC.scal.kap κ hK ⟨A3.A.μ0, p, hp, ?_⟩]
  · exact hκ
  · rw [RealDat3.prod_lamN]
    exact (Finset.prod_pos fun j _ ↦ hpos j _ p).ne'

end GlobalTheory.PosAtBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalLevelRelIndexLiftLevelEqCard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevIdx

open Formalism.IndefR.Lev (finE)

variable {D : D7} {T0 : Type} (C : LevCh D T0) (i : Fin D.R.m)

theorem mem_levG_datWp (P : LevelP C.Pg D.R.r ℂ) (κ : GA D (Wc D i)) :
    κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) ↔ κ ∈ GfC (Wc D i) ∧
      finE (Wc D i) κ ∈ parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i C.triv) ∧
      rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ) ∈ P.H := by
  rw [levG, Formalism.IndefR.Lev.mem_levA]
  refine and_congr_right fun _ => ?_
  exact Iff.rfl

def blkHom (P : LevelP C.Pg D.R.r ℂ) : levG (Wc D i) (C.βW i) (C.datWp i P) →* G0 C.Pg D.R.r where
  toFun κ := rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ.1)
  map_one' := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) 1) = 1
    rw [map_one]; exact rTup_one
  map_mul' x y := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) (x.1 * y.1)) = _
    rw [map_mul]
    exact rTup_mul (hc := D.sp.cm) (J := (Wc D i).gram) ((mem_levG_datWp C i P _).1 x.2).2.1
      ((mem_levG_datWp C i P _).1 y.2).2.1

theorem ker_blkHom (P : LevelP C.Pg D.R.r ℂ) :
    (blkHom C i P).ker = (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).subgroupOf
      (levG (Wc D i) (C.βW i) (C.datWp i P)) := by
  ext κ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_levG_datWp C i C.triv]
  obtain ⟨hG, hpar, -⟩ := (mem_levG_datWp C i P κ.1).1 κ.2
  constructor
  · intro h1
    exact ⟨hG, hpar, Subgroup.mem_bot.2 h1⟩
  · rintro ⟨-, -, hb⟩
    exact Subgroup.mem_bot.1 hb

theorem range_blkHom {μ0 : T0} (hC : C.Is μ0) (P : LevelP C.Pg D.R.r ℂ) : (blkHom C i P).range = P.H := by
  ext g
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨κ, rfl⟩
    exact ((mem_levG_datWp C i P κ.1).1 κ.2).2.2
  · intro hg
    obtain ⟨c, hB⟩ := hC.βW i
    have hsep := (GlobalTheory.StepLifts.places_apart C hC μ0).1
    obtain ⟨κ, hG, hpar, hred⟩ := GlobalTheory.ParahoricLift.liftsExist (Wc D i) (C.βW i) (C.datWp i C.triv) (C.ΛW i) _ hB
      (fun PP hPP PP' hPP' => hsep PP hPP PP' (hPP'.elim Or.inl fun h => absurd h (Finset.notMem_empty PP')))
      (Finset.disjoint_empty_right _) g
    have hmem : κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) := by
      refine (mem_levG_datWp C i P κ).2 ⟨hG, hpar, ?_⟩
      rw [hred]
      exact hg
    exact ⟨⟨κ, hmem⟩, hred⟩

theorem levidx : ∀ (D : D7) (T0 : Type) (C : LevCh D T0) (μ0 : T0), C.Is μ0 → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → C.Pg ⊆ Z → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) ∧ (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).relIndex (levG (Wc D i) (C.βW i) (C.datWp i P)) = Nat.card P.H ∧ Nat.card P.H ≠ 0 := by
  intro D T0 C μ0 hC _ _ _ _ i P
  have hle : levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) := by
    intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (mem_levG_datWp C i C.triv κ).1 hκ
    refine (mem_levG_datWp C i P κ).2 ⟨h1, h2, ?_⟩
    rw [Subgroup.mem_bot.1 h3]
    exact P.H.one_mem
  refine ⟨hle, ?_, Nat.card_pos.ne'⟩
  rw [Subgroup.relIndex, ← ker_blkHom C i P, Subgroup.index_ker, range_blkHom C i hC P]

end GlobalTheory.LevIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem adAt_mem_lieAt (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : adAt θ k τ X ∈ lieAt V τ := by

  have hU : Matrix.conjTranspose (infMat D.sp.cm.sig V.gram (θ τ) k) * gramAt D V τ *
      infMat D.sp.cm.sig V.gram (θ τ) k = gramAt D V τ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  exact skew_conj hU (GlobalTheory.Mem.AutSpace.infMat_mul_inv (θ := θ) (V := V) (τ := τ) (g := k)) hX

private theorem infMat_eq_one_of_mem_GfC {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) f = 1 := by

  have h1 : infHom V f = 1 := hf
  have h2 := congrArg (fun u => (u.val).map (θ τ)) h1
  simp only [Units.val_one] at h2
  rw [Matrix.map_one (θ τ) (map_zero (θ τ)) (map_one (θ τ))] at h2
  exact h2

private theorem adAt_mul_of_mem_GfC (a : GA D V) {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : adAt θ (a * f) τ X = adAt θ a τ X := by

  unfold adAt
  rw [mul_inv_rev, GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_eq_one_of_mem_GfC hf τ,
    infMat_eq_one_of_mem_GfC (inv_mem hf) τ, one_mul, mul_one]

theorem oneP_mul_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : oneP θ V τ X t * k = k * oneP θ V τ (adAt θ k τ X) t := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have hreal : IsRealPt θ a := ⟨ha, fun σ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a σ⟩
  have hinf : oneP θ V τ (adAt θ a τ X) t ∈ GinfC V := atTau_mem V τ _
  rw [adAt_mul_of_mem_GfC a hf, ← mul_assoc, oneP_mul hθ hreal hX t, mul_assoc, mul_assoc,
    comm_of_mem V hinf hf]

theorem Rder_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ (adAt θ k τ X) φ) := by

  funext g
  show deriv (fun t : ℝ => φ (g * oneP θ V τ X t * k)) 0 = deriv (fun t : ℝ => φ (g * k * oneP θ V τ (adAt θ k τ X) t)) 0
  congr 1
  funext t
  rw [mul_assoc, oneP_mul_adelic hθ k hX t, ← mul_assoc]

theorem rWord_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) (φ : GA D V → ℂ)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) :
    rWord θ V l (rTr V k φ) = rTr V k (rWord θ V (l.map fun p => (p.1, adAt θ k p.1 p.2)) φ) := by

  induction l with
  | nil => simp only [rWord, wordAct, List.foldr_nil, List.map_nil]
  | cons p l ih =>
    have hp : p.2 ∈ lieAt V p.1 := hl p List.mem_cons_self
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have ih' := ih hl'
    simp only [rWord, wordAct, List.foldr_cons, List.map_cons] at ih' ⊢
    rw [ih', Rder_rTr_adelic hθ k hp]

theorem rTr_mem_smFun (hθ : IsInfFam θ) (k : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    rTr V k φ ∈ SmFun θ V := by

  intro n τs Xs hXs g
  have key := hφ n τs (fun i => adAt θ k (τs i) (Xs i)) (fun i => adAt_mem_lieAt hθ k (hXs i)) (g * k)
  convert key using 1
  funext t
  show φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * k) =
    φ (g * k * (List.ofFn fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)).prod)
  rw [mul_assoc, prod_mul_eq k n (fun i => oneP θ V (τs i) (Xs i) (t i))
    (fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)) (fun i => oneP_mul_adelic hθ k (hXs i) (t i)),
    ← mul_assoc]

private theorem rapidDecSm_rTr_of_mem_GinfC (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) {φ : GA D V → ℂ}
    (h : RapidDecSm θ V φ) : RapidDecSm θ V (Formalism.L2.Theta.rTr V a φ) := by

  have hR := h.rapidDec.mul_right a
  refine ⟨⟨hR.1, ?_, hR.2.1⟩, rTr_mem_smFun hθ a h.smooth, fun l hl => ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U, hU, fun u hu huf g => ?_⟩
    show φ (g * u * a) = φ (g * a)
    rw [mul_assoc, ← comm_of_mem V ha huf, ← mul_assoc, hUφ u hu huf]
  · rw [rWord_rTr_adelic hθ a φ hl]
    refine (h.decay _ fun p hp => ?_).mul_right a
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact adAt_mem_lieAt hθ a (hl q hq)

theorem RapidDecSm.rTr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (k : GA D V) :
    RapidDecSm θ V (Formalism.L2.Theta.rTr V k φ) := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have e : Formalism.L2.Theta.rTr V (a * f) φ = Formalism.L2.Theta.rTr V a (Formalism.L2.Theta.rTr V f φ) := by
    funext g
    simp only [Formalism.L2.Theta.rTr, mul_assoc]
  rw [e]
  exact rapidDecSm_rTr_of_mem_GinfC hθ ha (h.rTr_fin hf)

end GlobalTheory.Size

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNeg
section
open MeasureTheory

namespace GlobalTheory

theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
end

