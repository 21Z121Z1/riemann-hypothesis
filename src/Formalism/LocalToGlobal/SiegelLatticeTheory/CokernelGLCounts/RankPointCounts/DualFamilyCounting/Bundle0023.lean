import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0023
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0021
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0033
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlgWitt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

private theorem s_inv_eq_of_s_eq_of_mul_eq_one {S : Type} [CommRing S] (s : S →+* S) (b b' : S) (hb : s b = b)
    (h : b * b' = 1) : s b' = b' := by
  have h1 : s b * s b' = 1 := by rw [← map_mul, h, map_one]
  rw [hb] at h1
  calc s b' = (b' * b) * s b' := by rw [mul_comm b' b, h, one_mul]
    _ = b' * (b * s b') := by ring
    _ = b' := by rw [h1, mul_one]

private theorem hform_transvection_preserves {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ z, s (s z) = z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : IsHerm s J) (v : Fin n → S) (b b' lam : S)
    (hvv : hform s J v v = b) (hbb : b * b' = 1) (hb' : s b' = b') (hlam : lam * s lam = 1)
    (z w : Fin n → S) :
    hform s J (z + ((s lam - 1) * (b' * hform s J v z)) • v)
      (w + ((s lam - 1) * (b' * hform s J v w)) • v) = hform s J z w := by
  have hzv : hform s J z v = s (hform s J v z) := (hform_conj s J hs hJ v z).symm
  simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
  rw [hzv, hvv]
  simp only [map_mul, map_sub, map_one, hs, hb']
  linear_combination (b' * hform s J v w * s (hform s J v z)) * hlam +
    (b' * hform s J v w * s (hform s J v z) * (lam - 1) * (s lam - 1)) * hbb

theorem algWitt : Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt := by
  unfold Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt
  intro S _ s O hs hsO n J J' hJ hJJ' hJO hJ'O a β β' hβO hβ'O hββ' hH x y hxO hyO hxx hyy

  have key : ∀ k : ℕ, k ≤ a → ∃ M : Matrix (Fin n) (Fin n) S,
      (∀ z w, hform s J (M *ᵥ z) (M *ᵥ w) = hform s J z w) ∧ (∀ i j, M i j ∈ O) ∧
      ∀ i : Fin a, i.val < k → M *ᵥ y i = x i := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, fun z w => by rw [Matrix.one_mulVec, Matrix.one_mulVec],
        fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hMp, hMO, hMy⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨i0, hi0⟩ : ∃ i0 : Fin a, i0.val = k := ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨yy, hyy_def⟩ : ∃ yy : Fin n → S, yy = M *ᵥ y i0 := ⟨_, rfl⟩
      have hyyO : ∀ l, yy l ∈ O := fun l => by
        rw [hyy_def]; exact mulVec_mem O M hMO (y i0) (hyO i0) l
      have htO : hform s J (x i0) yy ∈ O := hform_mem O s hsO J hJO (x i0) yy (hxO i0) hyyO
      obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := hH i0 (hform s J (x i0) yy) htO
      have hxx0 : hform s J (x i0) (x i0) = β i0 := by rw [hxx, if_pos rfl]
      have hyy0 : hform s J yy yy = β i0 := by rw [hyy_def, hMp, hyy, if_pos rfl]
      have hβr : s (β i0) = β i0 := by
        have h := hform_conj s J hs hJ (x i0) (x i0)
        rwa [hxx0] at h
      have hβ'r : s (β' i0) = β' i0 := s_inv_eq_of_s_eq_of_mul_eq_one s (β i0) (β' i0) hβr (hββ' i0)

      obtain ⟨u, hu_def⟩ : ∃ u : Fin n → S, u = yy - lam • x i0 := ⟨_, rfl⟩
      have huO : ∀ l, u l ∈ O := fun l => by
        rw [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hyyO l) (O.mul_mem hlamO (hxO i0 l))
      have huy : hform s J u yy = β i0 - s lam * hform s J (x i0) yy := by
        rw [hu_def, hform_sub_left, hform_smul_left, hyy0]
      have huu : hform s J u u =
          (β i0 - s lam * hform s J (x i0) yy) + s (β i0 - s lam * hform s J (x i0) yy) := by
        rw [hu_def]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right]
        rw [hyy0, hxx0, ← hform_conj s J hs hJ (x i0) yy]
        simp only [map_sub, map_mul, hs, hβr]
        linear_combination (β i0) * hlam
      have hcc : c' * (β i0 - s lam * hform s J (x i0) yy) = 1 := by rw [mul_comm]; exact hc'
      obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) S, T = rT s J u c' 1 := ⟨_, rfl⟩
      have hT_mul : ∀ z, T *ᵥ z = z - (c' * hform s J u z) • u := fun z => by
        rw [hT, rT_mulVec, map_one, one_smul]
      have hT_pres : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w := fun z w => by
        rw [hT]
        exact rT_preserves s J hs hJ u _ c' 1 (by rw [map_one, one_mul]) huu hcc z w
      have hT_O : ∀ i j, T i j ∈ O := fun i j => by
        rw [hT]; exact rT_mem O s hsO J hJO u huO c' 1 hc'O O.one_mem i j
      have hT_yy : T *ᵥ yy = lam • x i0 := by
        rw [hT_mul, huy, hcc, one_smul, hu_def, sub_sub_cancel]

      obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) S,
          D = 1 + (s lam - 1) • pM s J {i0} x β' := ⟨_, rfl⟩
      have hD_mul : ∀ z, D *ᵥ z = z + ((s lam - 1) * (β' i0 * hform s J (x i0) z)) • x i0 :=
        fun z => by
          rw [hD, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, pM_mulVec,
            Finset.sum_singleton, smul_smul]
      have hD_pres : ∀ z w, hform s J (D *ᵥ z) (D *ᵥ w) = hform s J z w := fun z w => by
        rw [hD_mul, hD_mul]
        exact hform_transvection_preserves s hs J hJ (x i0) (β i0) (β' i0) lam hxx0 (hββ' i0) hβ'r hlam z w
      have hD_O : ∀ i j, D i j ∈ O := fun i j => by
        rw [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j)
          (O.mul_mem (O.sub_mem (hsO lam hlamO) O.one_mem)
            (pM_mem O s hsO J hJO {i0} x hxO β' hβ'O i j))
      have hD_x : D *ᵥ (lam • x i0) = x i0 := by
        rw [hD_mul, hform_smul_right, hxx0]
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (x i0 l) * hlam + (x i0 l * (lam * s lam - lam)) * hββ' i0

      have hfix : ∀ i : Fin a, i.val < k → D *ᵥ (T *ᵥ x i) = x i := by
        intro i hi
        have hne : i0 ≠ i := fun h => by subst h; omega
        have h0 : hform s J u (x i) = 0 := by
          rw [hu_def, hform_sub_left, hform_smul_left, hxx i0 i, if_neg hne, ← hMy i hi, hyy_def,
            hMp, hyy i0 i, if_neg hne]
          ring
        rw [hT_mul, h0, mul_zero, zero_smul, sub_zero, hD_mul, hxx i0 i, if_neg hne, mul_zero,
          mul_zero, zero_smul, add_zero]
      refine ⟨D * T * M, fun z w => ?_, fun i j => ?_, fun i hi => ?_⟩
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hD_pres, hT_pres, hMp]
      · exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (D * T) M
          (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O D T hD_O hT_O i j) hMO i j
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · rw [hMy i hlt]; exact hfix i hlt
        · have hi' : i = i0 := Fin.ext (by omega)
          rw [hi', ← hyy_def, hT_yy, hD_x]
  obtain ⟨M, hMp, hMO, hMy⟩ := key a le_rfl
  have hU : cT s M * J * M = J := unitary_of s J M hMp
  have hNM : (J' * cT s M * J) * M = 1 := by
    calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hJJ']
  have hMN : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hNM
  refine ⟨⟨M, J' * cT s M * J, hMN, hNM⟩, ?_, fun i j => hMO i j, fun i j => ?_, fun i => hMy i i.isLt⟩
  · show cT s M * J * M = J
    exact hU
  · show (J' * cT s M * J) i j ∈ O
    exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (J' * cT s M) J
      (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O J' (cT s M) hJ'O
        (fun i j => cT_mem O s hsO M hMO i j) i j) hJO i j

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AssembleM
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cExpl_pos (h0 : HostDict) (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) :
    0 < cExpl D F0 what₂ := by
  obtain ⟨hK, hF, -⟩ := h0 D
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hc := (cMass_spec hK hF (D.R.k - 1) (by omega)).1
  have hd : 0 < |(NumberField.discr D.host.F : ℝ)| ^
      (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
    apply zpow_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hL : 0 < ∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← lValEta_eq_lValEtaF hK hF i hi2]
    exact lValEta_pos hK i hi2
  have hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂ := by
    intro Λ hΛ
    exact _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) (D.mem u).A.T (D.mem u).A.T_prime.pos F0 Λ
      (hR.2.2.1.1 Λ hΛ)
  have hm := Formalism.L2.SG.PairVal.massRows_pos D F0 what₂ hA hR.2.2.2
  unfold cExpl
  positivity

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem massAtUnif_of (h0 : HostDict) (hE : FormulaExplicit) : PI.UnitaryGroupMassFormula.CntFormula.MassAtUnif := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ
  refine ⟨cExpl D F0 what₂, cExpl_pos h0 D u F0 what₂ hR, fun Z hP => ?_⟩
  exact hE D δ M hA L u u' hT F0 what₂ hR.2.2.1 ϖ hϖ Z hP

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolOrdV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ¬ TypAt X v →
    localVolumeUnit X ψ v / ZZX X u u' ψ v =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))

def VolTypV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → ∀ v : PlX X, TypAt X v → localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))

def OmV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    (omAt X.B.I.cm.sig X.B.I.J ψ v ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
        Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) *
        aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')

def CondAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

def DiffProd : Prop :=
  HasProd (fun v : PlX X => absV v (dV v)) (|(NumberField.discr X.B.I.F : ℝ)|⁻¹)

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualEquivSymmApply
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual {Y : Type} [AddCommGroup Y] [Module K Y] [Module (𝓞 K) Y] [IsScalarTower (𝓞 K) K Y]
    {B : Y →ₗ⋆[K] Y →ₗ[K] K} {L : Submodule (𝓞 K) Y} {x : Y} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}

theorem push_dualIn (L : Submodule (𝓞 K) ↥X) :
    push X (dualIn (formOn h X) ⊤ L) = dualIn h X (push X L) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_dual.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact mem_dual.mp hx.2 y hy
  · rintro ⟨hvX, hv⟩
    refine ⟨⟨v, hvX⟩, ⟨by simp, mem_dual.mpr fun y hy => ?_⟩, rfl⟩
    exact mem_dual.mp hv _ (coe_mem_push.mpr hy)

variable {𝔭 : Ideal (𝓞 F)}

theorem map_incl_dual (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    (locF 𝔭 (dualIn (formOn h X) ⊤ L)).map (incl X) = locF 𝔭 (dualIn h X (push X L)) := by
  change push X _ = _
  rw [push_locF X hp, push_dualIn]

def dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L)) ≃ₗ[𝓞 K] ↥(locF 𝔭 (dualIn h X (push X L))) :=
  (Submodule.equivMapOfInjective (incl X) (incl_injective X) _).trans
    (LinearEquiv.ofEq _ _ (map_incl_dual hp L))

theorem dualEquiv_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    ((dualEquiv (h := h) hp L x : ↥(locF 𝔭 (dualIn h X (push X L)))) : V) = ((x : ↥X) : V) := rfl

theorem dualEquiv_symm_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    ((((dualEquiv (h := h) hp L).symm y : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) : ↥X) : V) = (y : V) := by
  have := dualEquiv_apply hp L ((dualEquiv (h := h) hp L).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem map_dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ((locF 𝔭 L).comap (locF 𝔭 (dualIn (formOn h X) ⊤ L)).subtype).map
        (dualEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) =
      (locF 𝔭 (push X L)).comap (locF 𝔭 (dualIn h X (push X L))).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← coe_mem_push (X := X), push_locF X hp]
  exact Iff.of_eq (congrArg (fun v => v ∈ locF 𝔭 (push X L)) (dualEquiv_symm_apply (h := h) hp L y))

def discEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    DiscMod (formOn h X) ⊤ L 𝔭 ≃ₗ[𝓞 K] DiscMod h X (push X L) 𝔭 :=
  Submodule.Quotient.equiv _ _ (dualEquiv (h := h) hp L) (map_dualEquiv (h := h) hp L)

theorem discEquiv_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    discEquiv (h := h) hp L (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dualEquiv (h := h) hp L x) := rfl

theorem discEquiv_symm_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    (discEquiv (h := h) hp L).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y) := rfl

def endEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    Module.End (𝓞 K) (DiscMod (formOn h X) ⊤ L 𝔭) ≃ Module.End (𝓞 K) (DiscMod h X (push X L) 𝔭) where
  toFun P := (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _)
  invFun P := ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _)
  left_inv P := by
    apply LinearMap.ext
    intro z
    simp
  right_inv P := by
    apply LinearMap.ext
    intro z
    simp

theorem discAut_push (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    discAut h X (push X L) 𝔭 = discAut (formOn h X) ⊤ L 𝔭 := by
  unfold discAut
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (endEquiv (h := h) hp L) ?_)
  intro P
  constructor
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x)) := by
      rw [← discEquiv_symm_mk, hx, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have hy' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y)) := by
      rw [← discEquiv_symm_mk, hy, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_symm_apply] using this
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk (dualEquiv (h := h) hp L x') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L x)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hx, discEquiv_mk]
    have hy' : Submodule.Quotient.mk (dualEquiv (h := h) hp L y') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L y)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hy, discEquiv_mk]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_apply] using this

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibPNeZeroOfGenus
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isLatIn_cut {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (X : Submodule K V) :
    IsLatIn X (Λ ⊓ X.restrictScalars (𝓞 K)) := by
  refine ⟨?_, le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    exact Submodule.FG.of_le_of_isNoetherian (inf_le_left : Λ ⊓ X.restrictScalars (𝓞 K) ≤ Λ)
  · obtain ⟨r, hr, hrx⟩ := StabilizerLattices.exists_smul_mem hΛ x
    have h1 : r • x ∈ Λ ⊓ X.restrictScalars (𝓞 K) := ⟨hrx, (X.restrictScalars (𝓞 K)).smul_mem r hx⟩
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    have e : x = (algebraMap (𝓞 K) K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem nondegenerate_of {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) :
    h.Nondegenerate := by
  constructor
  · exact hnd
  · intro y hy
    refine hnd y fun x => ?_
    rw [← hs.eq x y, hy x, map_zero]

theorem finite_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    (fibS h U 𝔭 M T).Finite := by
  have hp := h𝔭.isPrime
  have hN := isLattice_sup hUc hM hT
  have hD : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondegenerate_of hs hnd) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hN).1
  have hND := LIOrb.isLattice_inf hN hD
  have key : ∀ Λ ∈ fibS h U 𝔭 M T, locF 𝔭 (M ⊔ T) ≤ Λ ∧ Λ ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) ∧
      locF 𝔭 Λ = Λ := by
    rintro Λ ⟨⟨Λ', -, rfl⟩, h1, h2, h3⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ' := by
      have hs' : M ⊔ T ≤ locF 𝔭 Λ' := sup_le
        ((LocF.le_locF 𝔭 M).trans (h2 ▸ inf_le_left)) ((LocF.le_locF 𝔭 T).trans (h3 ▸ inf_le_left))
      exact (LocF.locF_mono 𝔭 hs').trans (LocF.locF_idem 𝔭 Λ').le
    refine ⟨hle, ?_, LocF.locF_idem 𝔭 Λ'⟩
    rw [G7.locF_dual hF h hN.fg hp]
    calc locF 𝔭 Λ' = dualF h 𝔭 (locF 𝔭 Λ') := h1.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
  refine Set.Finite.of_finite_image (f := fun Λ => Λ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T))
    ((BrB.finite_between hND hD inf_le_right).subset ?_) ?_
  · rintro _ ⟨Λ, hΛ, rfl⟩
    obtain ⟨k1, -, -⟩ := key Λ hΛ
    exact ⟨inf_le_inf_right _ ((LocF.le_locF 𝔭 _).trans k1), inf_le_right⟩
  · intro Λ₁ h1 Λ₂ h2 he
    obtain ⟨-, a1, b1⟩ := key Λ₁ h1
    obtain ⟨-, a2, b2⟩ := key Λ₂ h2
    have e1 : locF 𝔭 (Λ₁ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₁ := by
      rw [LIOrb.locF_inf_locF h𝔭, b1]; exact inf_eq_left.2 a1
    have e2 : locF 𝔭 (Λ₂ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₂ := by
      rw [LIOrb.locF_inf_locF h𝔭, b2]; exact inf_eq_left.2 a2
    rw [← e1, ← e2]
    exact congrArg (locF 𝔭) he

theorem fibP_ne_zero_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    fibP h U 𝔭 M T ≠ 0 ↔ (fibS h U 𝔭 M T).Nonempty := by
  have hfin := finite_fibS hF hs hnd hUc hM hT h𝔭
  rw [fibP_eq, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨x, hx⟩, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨⟨x, hx⟩⟩, hfin.to_subtype⟩

theorem fibP_congr (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M : Submodule (𝓞 K) V)
    {T T' : Submodule (𝓞 K) V} (e : locF 𝔭 T = locF 𝔭 T') : fibP h U 𝔭 M T = fibP h U 𝔭 M T' := by
  unfold fibP
  rw [e]

theorem fibP_ne_zero_of_genus (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hg : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : fibP h U 𝔭 M T ≠ 0 := by
  obtain ⟨g, hg, he⟩ := hg 𝔭 h𝔭
  have hT₀ := isLatIn_cut hΛ₀.1 (orthK h U)
  rw [← fibP_congr h U 𝔭 M (show locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))) = locF 𝔭 T
      by rw [← LocalizedFibreSets.gmap_locF, he]), G6.fibP_gmap hM 𝔭 _ hg,
    fibP_ne_zero_iff hF hs hnd hUc hM hT₀ h𝔭]
  exact ⟨_, locF_mem_fibS hF hΛ₀.1 hΛ₀.2.1 hΛ₀.2.2 rfl h𝔭⟩

end Formalism.L2.SG.Pf.G8
end
end

