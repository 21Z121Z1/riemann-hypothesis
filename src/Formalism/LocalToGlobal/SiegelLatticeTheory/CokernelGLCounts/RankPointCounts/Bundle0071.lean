import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0068
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0069
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DdPowConj
section
noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem ddPow_conj (Zd : LocDat D) {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).1 fun p =>
    Formalism.L2.SG.Pf.StabIntSh.locMem_conj Zd.δ Zd.M Zd.agree p hk
      ((Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).2 h p)

theorem mem_aaF {c b : Fin (D.R.rS + 1)} (hcb : c < b) {x y : D.host.E} (hx : x ∈ FibQ.aaF D b)
    (hy : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D (b.val - c.val)) : x * y ∈ FibQ.aaF D c := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  unfold FibQ.aaF Formalism.L2.SG.Pf.StabIntSh.ddPow at *
  rw [← zpow_add₀ (PI.NRCW.ddS_ne_zero D)] at h
  have e : -((D.R.rS : ℤ) - ((b : ℕ) : ℤ)) + -(((b.val - c.val : ℕ)) : ℤ) = -((D.R.rS : ℤ) - ((c : ℕ) : ℤ)) := by
    have : c.val ≤ b.val := le_of_lt hcb
    push_cast [this]
    ring
  rwa [e] at h

theorem sg_entry (B : Formalism.L2.SG.PairVal.MatR D) (c b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) c b =
      Formalism.L2.SG.Pf.StabIntSh.bt D B c b := by
  simp [Formalism.L2.SG.Pf.AtPt.Sg, Formalism.L2.SG.Pf.StabIntSh.bt, Matrix.mul_diagonal, Matrix.diagonal_mul]

end Formalism.L2.SG.Pf.FibD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdN
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdN_zorth : F0.z ∈ orth (VS D) (Xsp (lf D F0)) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F0.z x]
    have h := NMoveP.hT_f_X F0 (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem bwdN_znotX : F0.z ∉ Xsp (lf D F0) := by
  intro h
  have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 (bwdN_zorth (F0 := F0)) F0.z h
  rw [F0.z_norm, neg_eq_zero] at h0
  have hT := (D.mem u).A.T_prime.ne_zero
  exact hT (Nat.cast_eq_zero.1 h0)

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in

theorem bwdN_holds : BwdN Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨hΛ₂lat, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛlat : Submodule.IsLattice D.host.E γ.lam := hrow.2.1.1
  have ht1 := fun p => (hT2 p).1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    BwdNP.unit_of_frame Zd p γ (ht1 p).1.2.1 a
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (ht1 p).1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (ht1 p).1.2.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hLset : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f =
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => by
    have h := (hloc₂ p).2.1
    rw [hφ p] at h
    rw [← h]
    exact (Set.image_id _).symm
  have hSD := BwdNP.sd_of_loc Zd hΛlat hSDl
  have hSD₂ := BwdNP.sd_of_loc Zd hΛ₂lat hSDl₂
  set X := Xsp (lf D F0) with hXdef
  have hXiso : ∀ x ∈ X, ∀ y ∈ X, (VS D).hT x y = 0 := fun x hx y hy => NMoveP.hT_X_X F0 hx hy
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) X) → w ∈ X := fun {w} hw =>
    BwdNA.mem_of_orth_orth (VS D) X fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXo := BwdNA.X_le_orth (VS D) X hXiso
  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) X → ∃ y ∈ γ.lam, y - x ∈ X := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam hΛlat hSD (orth (VS D) X) x
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl (fun p => (hLset p).symm.subset) hx hxo hmΛ hmU)
    refine ⟨w, hw, ?_⟩
    have h2 := X.neg_mem (hXX hxw)
    rwa [neg_sub] at h2
  have hL' : ∀ y ∈ γ.lam, y ∈ orth (VS D) X → ∃ x ∈ Λ₂, x ∈ orth (VS D) X ∧ y - x ∈ X := fun y hy hyo => by
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂lat hSD₂ (orth (VS D) X) y
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl₂ (fun p => (hLset p).subset) hy hyo hmΛ hmU)
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) X).sub_mem hyo (hXo hX1)
  have hXm : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ γ.lam := fun x hx =>
    ⟨BwdNP.memX Zd γ hpr₂ hpr hΛlat hu hx, BwdNP.memX Zd γ hpr hpr₂ hΛ₂lat hu hx⟩
  have hy := BwdNP.exists_y Zd γ hΛ₂lat hSD₂ hpr₂ hu bwdN_znotX
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hiso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) X hXiso F0.z bwdN_zorth γ.lam Λ₂ hΛlat hΛ₂lat
    hSD hSD₂ hXm (BwdNP.z_mem Zd γ hΛlat hpr) (BwdNP.z_mem Zd γ hΛ₂lat hpr₂) hL hL' hy htr
  refine ⟨n, ⟨hiso, fun j x hx => ?_, hno, fun a => hnX _ (Submodule.subset_span ⟨a, rfl⟩), hnz⟩, himg⟩
  have hxX : x ∈ X := Submodule.span_mono (Set.image_subset_range _ _) hx
  rw [hnX x hxX, sub_self]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}

def wG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (VS D) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim (frame (lf D F0)) (frame F'₂)

def gramG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (VS D) D.R.rS T') :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i j => brS (VS D) (wG F0 F'₂ j) (wG F0 F'₂ i)

variable (Zd : LocDat D) (p : PlF D)

def sK : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b)

def sI : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val))
    (fun b => sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val))

theorem frFac_mul (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).pow _)

theorem sI_mul (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) : sI Zd p k * sK Zd p k = 1 := by
  cases k with
  | inl a =>
    show sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) * (sgnP D p a * frFac Zd.δ p a) = 1
    calc _ = (sgnP D p a * sgnP D p a) * (frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val)) := by ring
      _ = 1 := by rw [localSign_sq, frFac_mul, one_mul]
  | inr b =>
    show sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val) * (sgnP' D p b * frFac Zd.δ p b) = 1
    calc _ = (sgnP' D p b * sgnP' D p b) * (frFac Zd.δ p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val)) := by ring
      _ = 1 := by rw [sgnP'_sq, frFac_mul, one_mul]

variable {Zd p}

theorem split_none (hs : (Zd.M p).split = none) : (D.s.atP p).split = none := by
  have hA := (Zd.agree p).2.2.2.2.2
  rw [hs] at hA
  cases h2 : (D.s.atP p).split with
  | none => rfl
  | some sg =>
    rw [h2] at hA
    exact (hA : False).elim

theorem sI_mem (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O) (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    sI Zd p k ∈ (D.s.atP p).O := by
  have hs' := split_none hs
  have hT : Formalism.L2.SG.Pf.BBTie.btT Zd p ∈ (D.s.atP p).O :=
    Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ) hu
  cases k with
  | inl a =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP D p a ∈ _
    unfold TermLoc.sgnP
    rw [hs']
    exact Subring.one_mem _
  | inr b =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP' D p b ∈ _
    unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _

theorem cj_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) : (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map (((D.s.atP p).cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars
    𝒪[(D.s.atP p).Fp])

variable {u' : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq' (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = fun k => sK Zd p k • baseChange₂ D p (wG F0 F'₂ k) := by
  rw [vP_eq Zd γ F'₂ hs]
  funext k
  cases k <;> rfl

theorem gram_vP (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) :
    (locH Zd p).gram (vP Zd p γ F'₂) = Matrix.diagonal (fun k => (Zd.M p).L.cj (sK Zd p k)) *
      (gramG F0 F'₂).map (D.s.atP p).ιE * Matrix.diagonal (sK Zd p) := by
  rw [vP_eq' γ F'₂ hs]
  ext i j
  simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
    gramG]
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  ring

theorem gramInv_at (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hdet : (gramG F0 F'₂).det ≠ 0) (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hent : ∀ i j, (D.s.atP p).ιE ((gramG F0 F'₂)⁻¹ i j) ∈ (D.s.atP p).O) :
    Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂) := by
  have hO : (Zd.M p).L.O = (D.s.atP p).O := Formalism.L2.SG.Pf.LocalDenominators.hO Zd p
  have hcj : (Zd.M p).L.cj = (D.s.atP p).cj := Zd.hcj p
  set M := gramG F0 F'₂ with hMdef
  set ι := (D.s.atP p).ιE with hι
  refine ⟨Matrix.diagonal (sI Zd p) * M⁻¹.map ι * Matrix.diagonal (fun k => (Zd.M p).L.cj (sI Zd p k)),
    fun i j => ?_, ?_⟩
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
    rw [hO, hcj]
    exact Subring.mul_mem _ (Subring.mul_mem _ (sI_mem hs hδ hu i) (hent i j)) (cj_mem _ (sI_mem hs hδ hu j))
  · rw [gram_vP γ F'₂ hs]
    have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    have hmap : M⁻¹.map ι * M.map ι = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have hc1 : (fun k => (Zd.M p).L.cj (sI Zd p k) * (Zd.M p).L.cj (sK Zd p k)) = fun _ => 1 := by
      funext k; rw [← map_mul, sI_mul, map_one]
    have hs1 : (fun k => sI Zd p k * sK Zd p k) = fun _ => 1 := funext fun k => sI_mul Zd p k
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun k => (Zd.M p).L.cj (sI Zd p k)), Matrix.diagonal_mul_diagonal, hc1,
      Matrix.diagonal_one, Matrix.one_mul, ← Matrix.mul_assoc (M⁻¹.map ι), hmap, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, hs1, Matrix.diagonal_one]

end CohGoodPf

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂) in

def GlobGramNe : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
    Ctx γ Z → ZhatL (lf D F0) F'₂ = Z → (gramG F0 F'₂).det ≠ 0

theorem cohGood_of (hGG : GlobGramNe u u' F0 what₂) : CohGood Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  have hdet := hGG hP γ Z F'₂ hH.1 hH.2.1
  set X : Finset D.host.E := Finset.univ.image (fun ij : (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ×
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) => (gramG F0 F'₂)⁻¹ ij.1 ij.2) with hX
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree X
  rw [Filter.eventually_cofinite] at hgood
  refine hgood.subset fun p hp => ?_
  by_contra hn
  simp only [Set.mem_ofPred_eq, not_not] at hn
  apply hp
  obtain ⟨hs, hδ, hu, hXm⟩ := hn
  refine gramInv_at γ F'₂ hdet hs hδ.1 hu.1 fun i j => ?_
  by_cases h0 : (gramG F0 F'₂)⁻¹ i j = 0
  · rw [h0, map_zero]; exact Subring.zero_mem _
  · have hmem : (gramG F0 F'₂)⁻¹ i j ∈ X := Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩
    have h := (hXm _ hmem 0 (by simpa using h0)).1
    simpa using h

theorem star_coherence_of_gram (hLp : CohLp Zd u u' F0 what₂) (hGG : GlobGramNe u u' F0 what₂) :
    CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  star_coherence_of_good Zd hLp (cohGood_of Zd hGG)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRel
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormRelC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

end Formalism.L2.SG.Pf.FormRel

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel

theorem formNGC_of_rel (h : FormRelC) : Formalism.L2.SG.NGVanish.FormNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u').nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u' hx ν hν t hnz hv

theorem formGC_of_rel (h : FormRelC) : Formalism.L2.SG.Pf.MainEqVanish.FormGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u).nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u hx ν hν t hnz hv

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFstar
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem locFullC_holds : LocFullC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT p M hM
  exact Formalism.L2.SG.Pf.LocalDenominators.exists_isLattice_eq_localLattice Zd p M hM.1.1.1.1 hM.1.1.1.2.1

theorem patchC_holds : PatchC Zd u u' F0 what₂ := patchC_of_full Zd (locFullC_holds Zd u u' F0 what₂)

variable {Zd u u' F0 what₂}

theorem frGlob_of_fstar (hA : FStarC Zd u u' F0 what₂) : Formalism.L2.SG.Pf.PCount.FrGlob Zd u u' F0 what₂ :=
  frGlob_of Zd hA (patchC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf.MainEqFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ := ∏ p, L.aZ p (d p)

variable {D : D7}

theorem localLeG_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu,
      FamOKS N γ S C0n AAre (fun L => ampG L) Fm) :
    LocalInputLeG X N C1 C0n AAre := by
  intro γ hγ S
  obtain ⟨Fm, hR, hex, hOm, hD, hn, hV0, hrw, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  have hrank : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    rw [finrank_Vp]
    have h1 := D.R.r_eq
    have h2 : 2 * D.R.rS + 2 = D.R.m := by
      have hm2 := D.R.two_le_m
      obtain ⟨j, hj⟩ := D.R.m_even
      simp only [Formalism.BasicNotions.Ranks.rS]; omega
    omega
  have hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ) := fun p hp =>
    hQ (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p) (Z.agree p).1 (Vp D p) (locH Z p) (hrank p) (Fm.FP p) (hR p hp)
  have hq2 : ∀ p ∈ Fm.P, 2 ≤ LocNG.qF (D.s.atP p).Fp := fun p hp => Formalism.MainNotions.KappaEndpoints.two_le_residue_card (Z.agree p).1
  have hqH : ∀ p ∈ Fm.P, ¬ (Fm.FP p).PrimeTo → (LocNG.qF (D.s.atP p).Fp : ℝ) ≤ (Fm.FP p).Hp := fun p hp hpr =>
    Formalism.L2.SG.Pf.residue_le_height_nonprime (Z.agree p).1 (hR p hp) (hex p hp) hpr
  have hH1 : ∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp := by
    intro p hp
    by_cases hpr : (Fm.FP p).PrimeTo
    · exact le_of_eq ((hNG p hp (Fm.R p) (Fm.d0 p)).2.2.2 hpr).1.symm
    · have h2 : (2 : ℝ) ≤ (LocNG.qF (D.s.atP p).Fp : ℝ) := by exact_mod_cast hq2 p hp
      linarith [hqH p hp hpr]
  have hHp : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp := fun p hp => le_trans zero_le_one (hH1 p hp)
  have hB : Fm.toL.Basic := by
    refine ⟨fun p d => ?_, fun p => hH1 p.1 p.2, fun p => hq2 p.1 p.2, fun p hp => hqH p.1 p.2 ((hOm p).1 hp),
      fun p => ENNReal.toReal_nonneg, hV0, hrw⟩
    show 0 ≤ LocNG.Datum.wt (Fm.d0 p.1) d.1
    unfold LocNG.Datum.wt LocNG.volRel
    positivity
  exact ⟨Fm.toL, hB, (ngAt_toL Fm C1 hk hNG hD hn hHp).2, hM, hU, ha, hH, hpos, hle⟩

def StepFamG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

end Formalism.L2.SG.Pf.MainEqFam

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqFam

theorem stepLocPinnedG_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamG) : StepLocPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end Formalism.L2.SG.Pf
end
end

