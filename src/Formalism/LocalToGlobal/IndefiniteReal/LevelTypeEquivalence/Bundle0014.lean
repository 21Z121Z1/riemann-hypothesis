import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0009
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def kf (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Set (UI.instV fr).Gf :=
  {y | (y.1 : GL (Fin V.rank) (Lev.EAf D)) ∈ K}

theorem brg_mem_levA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : (UI.instV fr).GA) :
    UI.brg fr x ∈ Lev.levA V K ↔ x.1 = 1 ∧ x.2 ∈ kf fr K := by
  show UI.brg fr x ∈ GfC V ⊓ K.comap (Lev.finE V) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap, brg_mem_GfC, finE_brg]
  rfl

theorem kf_isCompact_isOpen_of_levelA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsLevelA V K) :
    IsCompact (kf fr K) ∧ IsOpen (kf fr K) := by
  have hpre : kf fr K = jf fr ⁻¹' (Lev.levA V K : Set (GA D V)) := by
    ext y
    show y ∈ kf fr K ↔ UI.brg fr (1, y) ∈ Lev.levA V K
    rw [brg_mem_levA]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact (jf_isClosedEmbedding fr).isCompact_preimage hK.1
  · have hmem : ∀ y, jf fr y ∈ GfC V := fun y => (brg_mem_GfC fr (1, y)).mpr rfl
    let jc : (UI.instV fr).Gf → GfC V := fun y => ⟨jf fr y, hmem y⟩
    have hjc : Continuous jc := (jf_isClosedEmbedding fr).continuous.subtype_mk _
    have e : kf fr K = jc ⁻¹' (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V)) := by
      rw [hpre]
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, jc]
    rw [e]
    exact hK.2.preimage hjc

def KstI : Subgroup (GL (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) :=
  Formalism.UG.stabGL (UI.instV fr).Lf

variable (V) in

def Kst : Subgroup (GL (Fin V.rank) (Lev.EAf D)) := KstI (UI.framesV D V)

theorem stabilizer_eq_level_subgroup : (UI.instV fr).Kset = {x : (UI.instV fr).Gf |
    (x : GL (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) ∈
      Formalism.UG.stabGL (lamAf (F := (UI.instV fr).F) (UI.instV fr).L) ∧
    ∀ y ∈ lamAf (F := (UI.instV fr).F) (UI.instV fr).L, ∃ z ∈ lamAf (F := (UI.instV fr).F) (UI.instV fr).L,
      ((x : GL (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) - 1 :
        Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) *ᵥ y =
        ((1 : ℕ) : (UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F) • z} := by
  ext x
  constructor
  · intro hx
    refine ⟨hx, fun y hy => ⟨_, Submodule.sub_mem _ ((hx y).mp hy) hy, ?_⟩⟩
    rw [Nat.cast_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  · intro hx
    exact hx.1

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MdTendstoSeq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem md_fun_succ (φ : WO S T → (Fin k → ℝ) → ℂ) (n : ℕ) (v : Fin (n + 1) → (Fin k → ℝ)) (h : ℝ) (a : Fin k → ℝ) :
    (fun y => md (φ y) (n + 1) v h a) = ((h : ℂ)⁻¹) • ((fun y => md (φ y) n (Fin.tail v) h (a + h • v 0)) +
      (-1 : ℂ) • (fun y => md (φ y) n (Fin.tail v) h a)) := by
  funext y
  simp only [md, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem md_theta {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {M : (Fin k → ℝ) →+ WO S T} (hM : IsRealFrame M) :
    ∀ (n : ℕ) (v : Fin n → (Fin k → ℝ)) (h : ℝ) (a : Fin k → ℝ),
      IsThetaFunO ψ S T (fun y => md (Gf ψ M f y) n v h a)
  | 0, v, h, a => by
    have : (fun y => md (Gf ψ M f y) 0 v h a) = heisO ψ S T (M a) f := rfl
    rw [this]
    exact thetaO_heis hψ hf (M a) ((wo_real_iff (M a)).mp (hM.2.1 a))
  | n + 1, v, h, a => by
    rw [md_fun_succ]
    exact thetaO_smul _ (thetaO_add (md_theta hψ hf hM n _ h _) (thetaO_smul _ (md_theta hψ hf hM n _ h _)))

theorem om_md {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (L : (Fin k → ℝ) →+ WO S T) (hL : IsRealFrame L) (g : GA D S)
    (h : GA D T) :
    ∀ (n : ℕ) (v : Fin n → (Fin k → ℝ)) (r : ℝ) (a : Fin k → ℝ),
      om (g, h) (fun y => md (Gf ψ ((actOAdd g⁻¹ h⁻¹).comp L) f y) n v r a) =
        fun x => md (Gf ψ L (om (g, h) f) x) n v r a
  | 0, v, r, a => by
    show om (g, h) (heisO ψ S T (actO S T g⁻¹ h⁻¹ (L a)) f) = heisO ψ S T (L a) (om (g, h) f)
    rw [hω.om_heis g h _ f hf, actO_inv]
  | n + 1, v, r, a => by
    rw [md_fun_succ, md_fun_succ (fun x => Gf ψ L (om (g, h) f) x), map_smul, map_add, map_smul,
      om_md hω hf L hL g h n, om_md hω hf L hL g h n]

theorem md_tendsto_seq {φ : (Fin k → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (v : Fin n → (Fin k → ℝ)) :
    Tendsto (fun j : ℕ => md φ n v (1 / ((j : ℝ) + 1)) 0) atTop (𝓝 (iteratedFDeriv ℝ n φ 0 v)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := md_tendsto n φ hφ v 0 (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_eq_norm]
  have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hlt : 1 / ((j : ℝ) + 1) < δ := by
    refine lt_of_le_of_lt ?_ hN
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hj
  exact lt_of_le_of_lt (hδε _ hpos hlt 0 (by simpa using hδ)) (by linarith)

end Formalism.IndefR.Eqv

end
end

