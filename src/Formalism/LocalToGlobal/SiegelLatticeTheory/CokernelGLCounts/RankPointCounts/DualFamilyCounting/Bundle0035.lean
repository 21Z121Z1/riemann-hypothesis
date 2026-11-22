import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0033
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CMeasSbox
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Phi

variable {ι : Type} [Fintype ι] {r k : ℕ}

def Φc (x : ∀ p : CBlk r, CSpc ι k p) (i : ι × LsNc5.CIdx r k) : ℝ :=
  match i with
  | (v, Sum.inl (Sum.inl (p, t))) => LsNc5.reim ((x (Sum.inl (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inl (Sum.inr (b, t))) => LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.last k)) t
  | (v, Sum.inr (Sum.inl (b, j, t))) =>
      LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.castSucc j)) t
  | (v, Sum.inr (Sum.inr (Sum.inl (p, t)))) => LsNc5.reim ((x (Sum.inr (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inr (Sum.inr (Sum.inr a))) => (x (Sum.inr (Sum.inr a)) : ι → ℝ) v

theorem measurable_Φc : Measurable (Φc (ι := ι) (r := r) (k := k)) := by
  refine measurable_pi_lambda _ fun i => ?_
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inl p) : CBlk r)))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.last k)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.castSucc j)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inr (Sum.inl p) : CBlk r)))
  · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inr (Sum.inr a) : CBlk r))

def Ψc (y : ι × LsNc5.CIdx r k → ℝ) : ∀ p : CBlk r, CSpc ι k p
  | Sum.inl (Sum.inl p) => fun v => (⟨y (v, Sum.inl (Sum.inl (p, false))), y (v, Sum.inl (Sum.inl (p, true)))⟩ : ℂ)
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ)
  | Sum.inr (Sum.inl p) => fun v =>
      (⟨y (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), y (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩ : ℂ)
  | Sum.inr (Sum.inr a) => fun v => y (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_Ψc (y : ι × LsNc5.CIdx r k → ℝ) : Φc (Ψc y) = y := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · cases t <;> rfl
  · have hj : ¬ (Fin.last k).val < k := by simp
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · have hj : (Fin.castSucc j).val < k := j.isLt
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · cases t <;> rfl
  · rfl

theorem Ψc_Φc (x : ∀ p : CBlk r, CSpc ι k p) : Ψc (Φc x) = x := by
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v; apply Complex.ext <;> rfl
  · funext v j
    show (if h : j.val < k then _ else _) = _
    split_ifs with h
    · apply Complex.ext
      · show LsNc5.reim (_ : ℂ) false = _
        simp only [LsNc5.reim, Bool.false_eq_true, if_false]
        congr 2
      · show LsNc5.reim (_ : ℂ) true = _
        simp only [LsNc5.reim, if_true]
        congr 2
    · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hj
      apply Complex.ext <;> rfl
  · funext v; apply Complex.ext <;> rfl
  · rfl

theorem measurable_Ψc : Measurable (Ψc (ι := ι) (r := r) (k := k)) := by
  have hC : ∀ f g : (ι × LsNc5.CIdx r k → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun y => (⟨f y, g y⟩ : ℂ) := fun f g hf hg =>
    Complex.measurableEquivRealProd.symm.measurable.comp (hf.prodMk hg)
  refine measurable_pi_lambda _ fun p => ?_
  rcases p with ((p | b) | (p | a))
  · exact measurable_pi_lambda _ fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · refine measurable_pi_lambda _ fun v => measurable_pi_lambda _ fun j => ?_
    show Measurable fun y : ι × LsNc5.CIdx r k → ℝ => (if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ))
    split_ifs with h
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact measurable_pi_lambda _ fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact measurable_pi_lambda _ fun v => measurable_pi_apply _

end Phi

section Box

variable {ι : Type} [Fintype ι] {r k : ℕ}

def cRow (b : Fin r) (j : Fin (k + 1)) (t : Bool) : LsNc5.CIdx r k :=
  if h : j.val < k then Sum.inr (Sum.inl (b, ⟨j.val, h⟩, t)) else Sum.inl (Sum.inr (b, t))

def Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) : ∀ p : CBlk r, Set (CSpc ι k p)
  | Sum.inl (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inl (Sum.inl (p, false))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inl (Sum.inl (p, true)))}
  | Sum.inl (Sum.inr b) => Set.univ.pi fun v => Set.univ.pi fun j : Fin (k + 1) =>
      {z : ℂ | LsNc5.reim z false ∈ s (v, cRow b j false) ∧ LsNc5.reim z true ∈ s (v, cRow b j true)}
  | Sum.inr (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, false)))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, true))))}
  | Sum.inr (Sum.inr a) => Set.univ.pi fun v => s (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_row (x : ∀ p : CBlk r, CSpc ι k p) (v : ι) (b : Fin r) (j : Fin (k + 1)) (t : Bool) :
    Φc x (v, cRow b j t) = LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j) t := by
  unfold cRow
  split_ifs with h
  · rfl
  · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    subst hj; rfl

theorem pre_box (s : ι × LsNc5.CIdx r k → Set ℝ) :
    Φc ⁻¹' Set.univ.pi s = Set.univ.pi (Sbox (ι := ι) (k := k) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h p
    rcases p with ((p | b) | (p | a))
    · intro v _; exact ⟨h (v, Sum.inl (Sum.inl (p, false))), h (v, Sum.inl (Sum.inl (p, true)))⟩
    · intro v _ j _
      refine ⟨?_, ?_⟩
      · have := h (v, cRow b j false); rwa [Φc_row] at this
      · have := h (v, cRow b j true); rwa [Φc_row] at this
    · intro v _; exact ⟨h (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), h (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩
    · intro v _; exact h (v, Sum.inr (Sum.inr (Sum.inr a)))
  · intro h i
    rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
    · have := h (Sum.inl (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.last k) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun t => by simp [cRow]
      have h2 := Φc_row x v b (Fin.last k) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.castSucc j) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) := fun t => by
        simp [cRow]
      have h2 := Φc_row x v b (Fin.castSucc j) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inr (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · exact h (Sum.inr (Sum.inr a)) v (Set.mem_univ v)

theorem cMeas_Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (p : CBlk r) :
    cMeas ι k p (Sbox s p) =
      match p with
      | Sum.inl (Sum.inl p) => ∏ v, volume (s (v, Sum.inl (Sum.inl (p, false)))) * volume (s (v, Sum.inl (Sum.inl (p, true))))
      | Sum.inl (Sum.inr b) => ∏ v, ∏ j : Fin (k + 1), volume (s (v, cRow b j false)) * volume (s (v, cRow b j true))
      | Sum.inr (Sum.inl p) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, false))))) *
          volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, true)))))
      | Sum.inr (Sum.inr a) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inr a)))) := by
  rcases p with ((p | b) | (p | a))
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → Fin (k + 1) → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun j _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℝ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]

theorem map_Φc : (Measure.pi (cMeas ι k (r := r))).map Φc = volume := by
  refine (Measure.pi_eq (μ := fun _ : ι × LsNc5.CIdx r k => (volume : Measure ℝ))
    (μ' := (Measure.pi (cMeas ι k (r := r))).map Φc) fun s hs => ?_).symm
  rw [Measure.map_apply measurable_Φc (MeasurableSet.univ_pi hs), pre_box, Measure.pi_pi]
  simp_rw [cMeas_Sbox s hs]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool, Fin.prod_univ_castSucc,
    Finset.prod_mul_distrib]
  have e1 : ∀ (b : Fin r) (t : Bool), cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun b t => by
    simp [cRow]
  have e2 : ∀ (b : Fin r) (j : Fin k) (t : Bool), cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) :=
    fun b j t => by simp [cRow]
  simp only [e1, e2]
  have swap : ∀ {β : Type} [Fintype β] (f : ι → β → ℝ≥0∞), ∏ v, ∏ b, f v b = ∏ b, ∏ v, f v b :=
    fun f => Finset.prod_comm
  simp only [swap]
  ring

end Box

theorem kap_eq_Φc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) :
    LsNc5.kap X u s = Φc (blk X u s) := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · rfl
  · show LsNc5.reim (LsNc5.yVec X u v s b) t = LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.last D.R.k)) t
    simp [blk]
  · show LsNc5.reim (LsNc5.phiMat X u v s b j) t =
      LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.castSucc j)) t
    simp [blk]
  · rfl
  · rfl

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowBlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS),
    Countable (cLat X u (Sum.inl (Sum.inr b))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inr b)))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensEqZeroOfNotMem
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem algebraMap_mem_LO (c : F) (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have h := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨c, hc⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h
  exact h

theorem dens_eq_zero_of_not_mem (H : Loc.HermSp M V) (ϖ : 𝒪[F]) {abelian₂ : Submodule M.L.O V} (hSD : H.IsSelfDual abelian₂)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (a b : ι) (hab : G₀ a b ∉ M.L.O) : H.dens ϖ abelian₂ G₀ = 0 := by
  unfold Loc.HermSp.dens
  have hE : IsEmpty {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} := by
    refine ⟨fun v => hab ?_⟩
    obtain ⟨hP, hG⟩ := v.2
    have h1 : H.h (v.1 b) (v.1 a) ∈ M.L.O := (hSD.2.2 (v.1 b)).1 (hP.1 b) (v.1 a) (hP.1 a)
    have h2 := hG a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
    have hϖ : algebraMap F E (ϖ : F) ∈ M.L.O := algebraMap_mem_LO _ ϖ.2
    have h3 : H.h (v.1 b) (v.1 a) - G₀ a b ∈ M.L.O := by
      rw [← hc]
      exact M.L.O.mul_mem c.2 hϖ
    have h4 : G₀ a b = H.h (v.1 b) (v.1 a) - (H.h (v.1 b) (v.1 a) - G₀ a b) := by ring
    rw [h4]
    exact M.L.O.sub_mem h1 h3
  have h0 : Set.range (fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
        fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)) = ∅ :=
    Set.range_eq_empty _
  rw [h0]
  simp

end Local

def GaPlusIntMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (∀ (p : PlF D) (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)),
          GaPlus M δ p (Tn u) (Tn u') Z a b ∈ (M p).L.O) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')

theorem notIntDens_of (h1 : LocSelfDual) (hG : GaPlusIntMM) : NotIntDens := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  by_contra hall
  push_neg at hall
  apply hI
  refine hG D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP fun p a b => ?_
  by_contra hab
  exact hall p (dens_eq_zero_of_not_mem (L.H p) (ϖ p) (h1 D δ M hA L p) _ a b hab)

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensProdValOf
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EtaLocD : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D),
    (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) = etaF D.host.E D.host.F p.asIdeal

theorem alpha_split' {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) {a b : ℕ} (hab : a ≤ b) :
    alphaStd K 𝔭 b = alphaStd K 𝔭 a *
      ∏ i ∈ Finset.Icc (a + 1) b, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
  unfold alphaStd
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc] at hi hi'
    omega

theorem densProdVal_of (hη : EtaLocD) : DensProdVal := by
  intro D δ M _ p c hc
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq := PI.UnitaryGroupMassFormula.CntFormula.residue_field_card D p
  have hmax : p.asIdeal.IsMaximal := p.isMaximal
  have hpos := alphaStd_pos hK hF hmax (D.R.k - 1 - c)
  rw [eq_div_iff hpos.ne', alpha_split' (K := D.host.E) p.asIdeal (show D.R.k - 1 - c ≤ D.R.r by omega), mul_comm]
  congr 1
  unfold Formalism.L2.SG.DensExact.densProd
  rw [hq, hη D p, show D.R.r + 1 - (2 * (D.R.rS + 1) + c) = D.R.k - 1 - c + 1 by omega]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [zpow_neg, zpow_natCast]

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsTotPosCongr
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_totPos_congr {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hne : 𝔭 ≠ ⊥) (a : 𝓞 F) (k : ℕ) :
    ∃ x : F, TotPos (algebraMap F K x) ∧ InP 𝔭 k (algebraMap F K ((a : F) + x)) := by
  have := h𝔭.isPrime
  have ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact pow_ne_zero _ hne
  have htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := Ideal.absNorm_mem _
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)
  have hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ htm
  have hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F) := by
    simp
  refine ⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩
  · intro φ
    rw [hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]
    have h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖ :=
      (Complex.re_le_norm _).trans (Finset.single_le_sum
        (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ))
    have h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)
    linarith
  · rw [add_sub_cancel]
    exact inP_of_mem_pow hz

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameRow : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ L : (LsNc5.CIdx D.R.rS D.R.k → ℝ) →ₗ[ℝ] (LsNc5.CIdx D.R.rS D.R.k → ℝ),
      (∀ s : X.B.I.Ginf, (fun i => LsNc5.kapV X w v s i) = L (fun i => LsNc5.kapV X u v s i)) ∧
      |LinearMap.det L| = (Tw w / Tw u) ^ D.R.rS

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfBasis
section
namespace Formalism.L2.SG.Pf.Cnt

theorem glueExists_of (hloc : Formalism.L2.SG.Pf.G7.GlueLocal) : GlueExists :=
  Formalism.L2.SG.Pf.G7.glueExists_of_local hloc

theorem glueExists_of_fam (hJ : JordanExists) (hV : Formalism.L2.SG.Pf.GluingBases.GlueVecs)
    (h0 : Formalism.L2.SG.Pf.GluingBases.FamTop) (h1 : Formalism.L2.SG.Pf.GluingBases.FamGram) (h2 : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of (Formalism.L2.SG.Pf.GluingBases.glueLocal_of_fam hJ hV h0 h1 h2 Formalism.L2.SG.Pf.FamilyMeetLattice.family_meet_holds)

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
section
namespace Formalism.L2.SG.Pf.NcVal

theorem volOrdV_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : VolOrdV X u u' ψ :=
  volOrdV_of X u u' ψ Formalism.L2.SG.Pf.conductor_inverse_different

end Formalism.L2.SG.Pf.NcVal
end

