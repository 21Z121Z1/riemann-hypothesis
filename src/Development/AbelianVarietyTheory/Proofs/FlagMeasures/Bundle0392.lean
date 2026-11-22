import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInvPowDifferentIffLocal
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

namespace GlobalTheory.DiffLoc

theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem mem_ddPow_neg_iff : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E,
    y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  intro D Z n hn y
  let a : Fin (D.R.rS + 1) := ⟨D.R.rS - n, by omega⟩
  have he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n := by
    show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n
    rw [Nat.cast_sub hn]; ring
  have hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
      ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) =
      Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
    intro p
    have h := locDiffC_holds D Z p a
    rw [he] at h
    exact h
  have hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1 := by
    intro p
    rw [bt_frFac_eq Z p a]
    have hk : D.R.rS - a.val = n := by show D.R.rS - (D.R.rS - n) = n; omega
    rw [hk]
    set U := (bt_T_unit Z p).unit
    have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
    rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]
  constructor
  · intro hy p
    have hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan p]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hm
    change (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]
    exact o.2
  · intro h
    rw [hinv]
    intro d hd
    rw [FractionalIdeal.mem_one_iff]
    have hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O := by
      intro p
      have hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
          (D.s.atP p).ιE d * x ∈ (Z.M p).L.O := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)
          rw [← map_mul, mul_comm, ← ho]
          exact bt_iota_int Z p o
        | zero => rw [mul_zero]; exact Subring.zero_mem _
        | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
        | smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem o.2 hx
      have hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O :=
        hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))
      have hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O := h p
      have e : (D.s.atP p).ιE (y * d) =
          ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a) := by
        calc (D.s.atP p).ιE (y * d) = (D.s.atP p).ιE y * (D.s.atP p).ιE d * (frFac Z.δ p a * btT Z p ^ n) := by
              rw [hf p, mul_one, map_mul]
          _ = _ := by ring
      rw [e]
      exact mul_mem hyp hdf
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc
    exact ⟨o, ho⟩

end GlobalTheory.DiffLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericTermClassesEqRowsInDoubleCoset
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowCls

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_apply {U : Submodule E S.V} {x : S.V} (hx : x ∈ orth S U) {y : S.V} (hy : y ∈ U) :
    S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
  exact hx y hy

theorem mem_orth_of {U : Submodule E S.V} {x : S.V} (h : ∀ y ∈ U, S.hT y x = 0) : x ∈ orth S U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  exact h

theorem mem_orth_Xsp {T : E} (F : LFlag S r T) (x : S.V) (hx : ∀ a, S.hT (F.fl.e a) x = 0) :
    x ∈ orth S (Xsp F) := by
  refine mem_orth_of fun y hy => ?_
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hx a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_orth_Xsp {T : E} (F : LFlag S r T) (i : Fin (r + 1)) (y : S.V) (hy : y ∈ Xsp F) :
    S.hT (F.fl.fvec i) y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    induction i using Fin.lastCases with
    | last => rw [FlagG.fvec, Fin.snoc_last, ← S.herm.eq, F.fl.z_orth b, map_zero]
    | cast a => rw [FlagG.fvec, Fin.snoc_castSucc]; exact F.fl.e_iso a b
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem mapLF_fvec {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T)
    (i : Fin (r + 1)) : (mapLF γ F).fl.fvec i = γ (F.fl.fvec i) := by
  unfold mapLF
  rw [dif_pos hγ]
  induction i using Fin.lastCases with
  | last => simp [FlagG.fvec, mapFlag]
  | cast a => simp [FlagG.fvec, mapFlag]

end Gen

section NR

variable {D : D7}

theorem nrat_fvec_sub {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) (i : Fin (D.R.rS + 1)) : n (F.fl.fvec i) - F.fl.fvec i ∈ Xsp F := by
  induction i using Fin.lastCases with
  | last =>
    rw [FlagG.fvec, Fin.snoc_last]
    exact hn.2.2 _ (mem_orth_Xsp F _ F.fl.z_orth)
  | cast a =>
    rw [FlagG.fvec, Fin.snoc_castSucc]
    have h1 : F.fl.e a ∈ Xflag F (a.1 + 1) :=
      Submodule.subset_span ⟨a, by show a.1 < a.1 + 1; omega, rfl⟩
    exact Submodule.span_mono (Set.image_subset_range _ _) (hn.2.1 a.1 _ h1)

theorem nrat_map_Xsp {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) (y : (VS D).V) (hy : y ∈ Xsp F) : n y ∈ Xsp F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h := nrat_fvec_sub F hn a.castSucc
    rw [FlagG.fvec, Fin.snoc_castSucc] at h
    have h2 : F.fl.e a ∈ Xsp F := Submodule.subset_span ⟨a, rfl⟩
    simpa using (Xsp F).add_mem h h2
  | zero => simp
  | add y y' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul c y _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

theorem one_mem_NRat {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

end NR

end GlobalTheory.Unfold.RowCls

namespace GlobalTheory.Unfold.RowCls

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nonGeneric_terms_same_coset_corank_one (t t' : TauC Y u u') (ht : t ∈ (Y.tO u u').ngSet) (hlam : t.lam = t'.lam)
    (hlam' : t.lam' = t'.lam') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NRat (lf D (X.Fu u)))
    (n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn' : n' ∈ NRat (lf D (X.Fu u'))) (he : t'.lin = n * t.lin * n') :
    (Y.tO u u').s0 t t' = 1 := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : Submodule.IsLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact t'.rep.2.2.2.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hiso' : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  show Formalism.L2.SG.TermOp.s0T t t' = 1
  unfold Formalism.L2.SG.TermOp.s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  refine (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 ?_
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp _ _ _ _ _) fun x hx => ?_
  have hxo : ∀ i, (VS D).hT (Sum.elim (lf D (X.Fu u)).fl.fvec t.frame.fl.fvec i) x = 0 := fun i =>
    Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp t.lam _ t.frame hx
      (PI.PairCorankPos.W.frame_mem_UUE t.lam hlat _ t.frame hLF hLt i)
  have hxF : x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
    mem_orth_Xsp _ x fun a => by simpa [FlagG.fvec] using hxo (Sum.inl a.castSucc)
  have hxt : x ∈ orth (VS D) (Xsp t.frame) :=
    mem_orth_Xsp _ x fun a => by simpa [FlagG.fvec] using hxo (Sum.inr a.castSucc)

  have hXt : ∀ d ∈ Xsp (lf D (X.Fu u')), t.lin d ∈ Xsp t.frame := fun d hd =>
    (Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF t.lin hiso (lf D (X.Fu u')) _).2 (by simpa using hd)
  refine Submodule.mem_map.2 ⟨(x, n x), (Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs _ _ _ _ _ _).2 ⟨hx, ?_, ?_, ?_⟩, rfl⟩
  · refine Formalism.L2.SG.NGCut.CorankRelation.mem_Hp_of_orth t.lam _ t'.frame hLF hL' (n x) ?_
    rintro (a | b)
    · show (VS D).hT ((lf D (X.Fu u)).fl.fvec a) (n x) = 0
      have h1 : (VS D).hT ((lf D (X.Fu u)).fl.fvec a) x = 0 := hxo (Sum.inl a)
      have h2 := frame_orth_Xsp (lf D (X.Fu u)) a _ (hn.2.2 x hxF)
      have h3 : n x = x + (n x - x) := by abel
      rw [h3, map_add, h1, h2, add_zero]
    · show (VS D).hT (t'.frame.fl.fvec b) (n x) = 0
      have hf : t'.frame.fl.fvec b = n (t.lin (n' ((lf D (X.Fu u')).fl.fvec b))) := by
        show (mapLF t'.lin (lf D (X.Fu u'))).fl.fvec b = _
        rw [mapLF_fvec t'.lin hiso' _ b, he]
        rfl
      rw [hf, hn.1]
      have hd := nrat_fvec_sub (lf D (X.Fu u')) hn' b
      have h4 : n' ((lf D (X.Fu u')).fl.fvec b) =
          (lf D (X.Fu u')).fl.fvec b + (n' ((lf D (X.Fu u')).fl.fvec b) - (lf D (X.Fu u')).fl.fvec b) := by abel
      have h5 : (VS D).hT (t.lin ((lf D (X.Fu u')).fl.fvec b)) x = 0 := by
        have := hxo (Sum.inr b)
        simp only [Sum.elim_inr] at this
        rwa [show t.frame.fl.fvec b = t.lin ((lf D (X.Fu u')).fl.fvec b) from mapLF_fvec t.lin hiso _ b] at this
      rw [h4, map_add, map_add, LinearMap.add_apply, h5, orth_apply hxt (hXt _ hd), add_zero]
  · show x - n x ∈ Xsp (lf D (X.Fu u))
    have := (Xsp (lf D (X.Fu u))).neg_mem (hn.2.2 x hxF)
    simpa using this
  · show (t'.lin * t.lin⁻¹) x - n x ∈ Xsp t'.frame
    refine (Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF t'.lin hiso' (lf D (X.Fu u')) _).2 ?_
    set w := t.lin.symm x with hw
    have hwx : t.lin w = x := by simp [hw]
    have key : t'.lin (w - n'.symm w) = (t'.lin * t.lin⁻¹) x - n x := by
      rw [he]
      show n (t.lin (n' (w - n'.symm w))) = n (t.lin (n' (t.lin.symm x))) - n x
      rw [← hw, map_sub, LinearEquiv.apply_symm_apply, map_sub, map_sub, hwx]
    rw [← key, LinearEquiv.symm_apply_apply]

    have hwo : ∀ y ∈ Xsp (lf D (X.Fu u')), (VS D).hT y w = 0 := fun y hy => by
      rw [← hiso y w, hwx]
      exact orth_apply hxt (hXt y hy)
    have hv : n'.symm w ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) := by
      refine mem_orth_of fun y hy => ?_
      rw [← hn'.1 y (n'.symm w), LinearEquiv.apply_symm_apply]
      exact hwo _ (nrat_map_Xsp _ hn' y hy)
    have h6 := hn'.2.2 _ hv
    rw [LinearEquiv.apply_symm_apply] at h6
    exact h6

theorem clsRow_ngSet : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    ClsRow (Y.tO u u').ngSet (clsOf Y u u') := by
  intro D X Y u u' hT t ht t' ht' hn
  obtain ⟨hR, hS, hTr⟩ := Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds D X Y u u' hT
  have hiff : clsOf Y u u' t = clsOf Y u u' t' ↔
      ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ (Y.tO u u').s0 t t' = 1) := by
    constructor
    · intro heq
      have hm : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hR t' ht'⟩
      rw [← heq] at hm
      exact ⟨hm.2.1.symm, hm.2.2⟩
    · rintro ⟨hr, hs⟩
      ext x
      simp only [Formalism.L2.SG.RowsConc.clsOf, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hx, hrx, hsx⟩
        exact ⟨hx, hrx.trans hr, hTr t' ht' t ht x hx hr.symm hrx.symm (hS t ht t' ht' hr hs) hsx⟩
      · rintro ⟨hx, hrx, hsx⟩
        exact ⟨hx, hrx.trans hr.symm, hTr t ht t' ht' x hx hr hrx.symm hs hsx⟩
  rw [hiff]
  refine ⟨fun h => h.1, fun hr => ⟨hr, ?_⟩⟩
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]
    exact ⟨1, one_mem_NRat _, 1, one_mem_NRat _, by simp⟩
  obtain ⟨n, hnn, n', hnn', he⟩ := hmem
  exact nonGeneric_terms_same_coset_corank_one t t' ht hlam hlam' n hnn n' hnn' he

end Terms

end GlobalTheory.Unfold.RowCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroCmElementLocalUnitAlmostAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitAlmostAll

variable {D : D7}

theorem exists_nat_mul_integral (x : D.host.E) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : D.host.E) * x) := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ D.host.E := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple

  refine ⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩
  have hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := by
    rw [Nat.cast_mul]
    exact Int.natAbs_mul_self' y
  have e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x) := by
    rw [zsmul_eq_mul, ← mul_assoc]
    have hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E) :=
      (Int.cast_natCast _).symm
    rw [hc, hsq, Int.cast_mul]
  rw [e]
  have hyi : IsIntegral ℤ (y : D.host.E) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))
  exact hyi.mul hy

theorem iota_mem_O (Z : LocDat D) (p : PlF D) (x : D.host.E) (n : ℕ)
    (hint : IsIntegral ℤ ((n : D.host.E) * x)) (hn : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)) :
    (D.s.atP p).ιE x ∈ (Z.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocFacts.lf_hO Z p, (D.s.atP p).O_def]
  have : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp) := map_natCast _ n
  have hc0 : (n : (D.s.atP p).Fp) ≠ 0 := by exact_mod_cast hn0

  have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn
    rwa [map_natCast] at this
  have hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
    have := ((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])
    rwa [map_one, hcn] at this
  have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1
      (n : (D.s.atP p).Fp)).mp hle
    rw [map_one] at h1
    exact inv_le_one_of_one_le₀ h1
  have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ *
      (D.s.atP p).ιE ((n : D.host.E) * x) := by
    have hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F) := (map_natCast _ n).symm
    rw [map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [hx]
  refine IsIntegral.mul ?_ ?_
  · exact isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)
  · exact (hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top

theorem unit_almost_all : ∀ (D : D7) (Z : LocDat D) (x : D.host.E), x ≠ 0 →
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE x)}.Finite := by
  intro D Z x hx
  obtain ⟨n, hn0, hn⟩ := exists_nat_mul_integral x
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_integral x⁻¹

  have hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero hn0 hm0
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hnm
  apply hp
  have hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_right _ _ h)
  have hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_left _ _ h)
  refine ⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]

end GlobalTheory.UnitAlmostAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

theorem iota_int_cofinite {D : D7} (Z : LocDat D) (x : D.host.E) :
    {p : PlF D | (D.s.atP p).ιE x ∉ (Z.M p).L.O}.Finite := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = y.natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by rw [hn]; exact Int.natAbs_ne_zero.2 hy0
  have hint' : IsIntegral ℤ ((n : D.host.E) * x) := by
    rcases Int.natAbs_eq y with h | h <;> rw [← hn] at h
    · have e : y • x = (n : D.host.E) * x := by
        rw [zsmul_eq_mul, h, Int.cast_natCast]
      rw [← e]; exact hint
    · have e : y • x = -((n : D.host.E) * x) := by
        rw [zsmul_eq_mul, h, Int.cast_neg, Int.cast_natCast, neg_mul]
      have := hint.neg
      rw [e, neg_neg] at this
      exact this
  let w : 𝓞 D.host.E := ⟨(n : D.host.E) * x, hint'⟩
  have hfin : {p : PlF D | Loc.resChar p ∣ n}.Finite := by
    have hne : (Ideal.span {((n : ℕ) : 𝓞 D.host.F)} : Ideal (𝓞 D.host.F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hn0
    refine (Ideal.finite_factors hne).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, bt_natCast_mem_iff]
    exact hp
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra hnd
  apply hp
  obtain ⟨_, w', hw'O, hw'⟩ := bt_nat_unit Z p n hnd
  have hwO := bt_iota_int Z p w
  have e : (D.s.atP p).ιE x = w' * (D.s.atP p).ιE (w : D.host.E) := by
    show _ = w' * (D.s.atP p).ιE ((n : D.host.E) * x)
    rw [map_mul, map_natCast, ← mul_assoc, hw', one_mul]
  rw [e]
  exact Subring.mul_mem _ hw'O hwO

theorem tri_scaled : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g →
    ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧
      {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  intro D Z f g A hA hg
  refine ⟨fun p a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b), ?_, ?_⟩
  · intro p
    refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
    · simp [hA.1 a b hab]
    · show Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a * (D.s.atP p).ιE (A a a) = 1
      rw [hA.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)]
    · simp only [scaled]
      rw [hg b, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [baseChange_smul₂, smul_smul, smul_smul]
      congr 1
      have h := Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)
      linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h
  · have hD := locDiffC_holds D Z
    refine (Set.Finite.biUnion (Set.finite_univ (α := Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
      (fun ab _ => iota_int_cofinite Z (A ab.1 ab.2))).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, not_forall] at hp
    obtain ⟨a, b, hab⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, exists_true_left]
    refine ⟨(a, b), ?_⟩
    intro hι
    apply hab
    rcases lt_or_ge b a with h | h
    · simp [hA.1 a b h]
    · obtain ⟨k, hk, hkb⟩ := bt_frFac_step Z p hD a b h
      have e : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b) =
          k * (D.s.atP p).ιE (A a b) := by
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a), one_mul]
      rw [e]
      exact Subring.mul_mem _ hk hι

end GlobalTheory.LocOver
end
end

