import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTestBOfRatG
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.LiftTestCompare GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.LiftRat Formalism.IndefR.Cx Formalism.IndefR.Rat

namespace GlobalTheory.TwistField

section Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def readBasis (hU : R.LUnif) (i : Fin D.R.m) :
    Module.Basis (Fin (R.nW i)) ℂ (Tw (twAt D.what₂.embLL A.v0) (R.HW i (sg0 D A)).H) :=
  Module.Basis.mk (Tw.linInd _ ((hU i (sg0 D A)).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent))
    (Tw.span_top _ (span_basis R hU i (sg0 D A))).ge

theorem readBasis_coord (hU : R.LUnif) (i : Fin D.R.m) (y : Fin (R.nW i) → D.what₂.LL) (k : Fin (R.nW i)) :
    (readBasis R hU i).coord k (Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y)) = A.v0.embedding (y k) := by
  have h1 : Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y) = ∑ l, A.v0.embedding (y l) • readBasis R hU i l := by
    rw [j_eq_sum]
    refine Finset.sum_congr (M := (R.HW i (sg0 D A)).H) rfl fun l _ => ?_
    rw [readBasis, Module.Basis.mk_apply]
    show _ = cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y l)) •
      (R.FW i).j (sg0 D A) (Pi.basisFun D.what₂.LL (Fin (R.nW i)) l)
    rw [emb_eq D.what₂.embLL A.v0, cj_cj]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

end Read

theorem liftTestB_of_ratG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool), R.toRealDat.LUnif → GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) b := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hU hG
  rw [toCx3_liftTestB]
  intro j
  refine ⟨R.toRealDat.nW j, fun k => (readBasis R.toRealDat hU j).coord k,
    fun w hw => (readBasis R.toRealDat hU j).forall_coord_eq_zero_iff.1 hw, ?_, ?_⟩
  · intro t k x
    obtain ⟨y, hy⟩ := hG j t x
    refine ⟨y k, ?_⟩
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.toRealDat.thG j t (R.toRealDat.jV j t x)))
    rw [← hy, readBasis_coord]
    rfl
  · intro k (l : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)))
    refine ⟨R.toRealDat.bL F.lv2 b j l k, ?_⟩
    have hc : cpt A3.A.v0.embedding (Pi.single l (1 : D.what₂.LL)) = Pi.single l 1 := by
      funext r
      by_cases h : r = l
      · subst h; simp [cpt]
      · simp [cpt, Pi.single_apply, h]
    have h : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1)) = (R.toRealDat.FW j).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b j l) := by
      have h0 := liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 b j (Pi.single l 1)
      have e1 : ∑ k, (Pi.single l (1 : D.what₂.LL) : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)) → D.what₂.LL) k • R.toRealDat.bL F.lv2 b j k = R.toRealDat.bL F.lv2 b j l := by
        simp [Pi.single_apply]
      rw [e1] at h0
      refine Eq.trans ?_ h0
      erw [hc] <;> rfl
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1))))
    rw [h, readBasis_coord]
    rfl

end GlobalTheory.TwistField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftWeightComplexPointEqTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjScalarCoord

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)

theorem wC_cpt (j : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
        (R.FW j).j (sgAt D.what₂.embLL v) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      ((∑ k, cj (twAt D.what₂.embLL v) (v.embedding (c k)) •
        (⟨R.toRealDat.bC F.lv2 b j _ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) :
        (R.HW j (sgAt D.what₂.embLL v)).H) := rfl
  rw [e, Submodule.coe_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, emb_eq D.what₂.embLL v, cj_cj, LinearMap.map_smulₛₗ, smul_comm]
  rfl

theorem sqrt_ne : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'

theorem liftWeight_complexPoint_eq_twist (j : Fin D.R.m) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      (R.FW j).j (sg0 D A3.A) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • ((Tw.out (s := twAt D.what₂.embLL A3.A.v0)
        ((R.toCx3 F).wC b j A3.A.v0 (cpt A3.A.v0.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL A3.A.v0)) : (R.HW j (sgAt D.what₂.embLL A3.A.v0)).H) := rfl
  rw [e, wC_cpt, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem inner_wC (j : Fin D.R.m) {v : InfinitePlace D.what₂.LL} (hv : v ≠ A3.A.v0) (c c' : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      (Nat.card (F.lv2.lvl b).P : ℂ)⁻¹ * ⟪(R.FW j).j v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b j k),
        (R.FW j).j v.embedding (∑ k, c' k • R.toRealDat.bL F.lv2 b j k)⟫_ℂ := by
  have hs : sgAt D.what₂.embLL v = v.embedding := if_neg (R.hv0 ▸ hv)
  have ht : twAt D.what₂.embLL v = false := if_pos hs.symm
  have e : ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      cj (twAt D.what₂.embLL v) ⟪((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H),
        ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c')) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H)⟫_ℂ := rfl
  rw [e, wC_cpt, wC_cpt, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (RealDat.nP_pos (F := F.lv2) b).le, hs]
  generalize twAt D.what₂.embLL v = s at ht
  subst ht
  simp only [cj, RealDat.nP, Bool.false_eq_true, if_false]
  simp only [cond_false, RingHom.id_apply, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem tC_cpt (cr : Crd A3.fam3.amb3 F.fc) (j : Fin D.R.m) (t : T0)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) b).dZ j t) → D.what₂.LL) :
    (R.toCx3 F).tC cr b j t (cpt A3.fam3.base3.v0.embedding x) =
      (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t (cr.toL (R.toCx3 F).zs b j t x)) := by
  conv_rhs => rw [← (Pi.basisFun D.what₂.LL _).sum_repr x]
  simp only [CxData.tC, lin_apply, map_sum, map_smul, LinearMap.map_smulₛₗ, Pi.basisFun_repr, Pi.basisFun_apply, cpt,
    RingHom.id_apply]

theorem liftMat_isRatLift_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).H5 F.cr false → (R.toCx3 F).RATth F.cr false → ∀ i, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R.toRealDat i (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k)) ∧ ∀ v, v ≠ A3.A.v0 → ∀ x y, ⟪(R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x)), (R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y))⟫_ℂ = ((Nat.card F.P0 : ℕ) : ℂ)⁻¹ * ⟪(R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k), (R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y) k • R.toRealDat.bL F.lv2 false i k)⟫_ℂ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hR i
  refine ⟨fun x => ?_, fun v hv x y => ?_⟩
  · show (R.FW i).j (sg0 D A3.A) _ = _
    refine (liftWeight_complexPoint_eq_twist R F false i _).symm.trans ?_
    have h1 := ((R.toCx3 F).key_lift F.cr false hT hR i A3.A.μ0 x).trans (tC_cpt R F false F.cr i A3.A.μ0 x)
    exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) h1
  · rw [inner_wC R F false i hv]
    rfl

end GlobalTheory.ConjScalarCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapMulMtEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.RowMat

theorem map_coord_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (f : V → V) (hf : Measurable f)
    (hfH : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map f = μ) (ρ : ℕ)
    [inst : MeasurableSpace (Fin ρ → V)] [hB : BorelSpace (Fin ρ → V)]
    (lam : Measure (Fin ρ → V)) [hlam : lam.IsAddHaarMeasure] :
    lam.map (fun b i => f (b i)) = lam := by
  have e : inst = MeasurableSpace.pi :=
    hB.measurable_eq.trans (@BorelSpace.measurable_eq (Fin ρ → V) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have hp : MeasurePreserving f (Measure.addHaar : Measure V) Measure.addHaar :=
    ⟨hf, hfH _ inferInstance⟩
  rw [Measure.isAddLeftInvariant_eq_smul lam (Measure.pi fun _ : Fin ρ => (Measure.addHaar : Measure V)),
    Measure.map_smul]
  congr 1
  exact (measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)).map_eq

theorem map_mul_mt_eq : ∀ (D : D7) (S₀ : HSp D) (ρ : ℕ) (lam : Measure (Mx D ρ S₀.rank)),
    lam.IsAddHaarMeasure → ∀ h : GA D S₀,
      lam.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) = lam := by
  intro D S₀ ρ lam hlam h
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hrow := GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm.1 S₀.rank S₀.gram
    (hcm.2 S₀) h
  have e : (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) =
      fun b i => Matrix.vecMul (b i) (mt S₀ h) := by
    funext b i j
    rfl
  rw [e]
  have hm : Measurable (fun x : Fin S₀.rank → AE D => Matrix.vecMul x (mt S₀ h)) :=
    (Continuous.matrix_vecMul continuous_id continuous_const).measurable
  exact map_coord_eq (V := Fin S₀.rank → AE D) (f := fun x => Matrix.vecMul x (mt S₀ h)) (hf := hm)
    (hfH := fun μ hμ => hrow μ hμ) (ρ := ρ) (inst := measMx ρ S₀.rank)
    (hB := @BorelSpace.mk _ _ (measMx ρ S₀.rank) rfl) (lam := lam) (hlam := hlam)

end GlobalTheory.AdelicModulus.RowMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchUpOfTr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatchUpProof

theorem matchUp_of_tr : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.TrCopy.TRLev R F SF → MatchUp R SF := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hTR c hE i

  have hHE := hC.models.HE
  unfold RealDat.models_HE at hHE
  obtain ⟨hinjE, hrngE, -⟩ := hHE

  have hHW := hC.models.HW
  unfold RealDat.models_HW at hHW
  obtain ⟨-, hrngW, -⟩ := hHW i (sg0 D A)

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hE
  have hE' : TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) R.e0 SF c ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨R.HE.e x, Submodule.mem_inf.2 ⟨hx, ?_⟩, ?_⟩
    · have hmem : R.HE.e x ∈ LinearMap.range R.HE.e := LinearMap.mem_range_self _ x
      rw [hrngE] at hmem
      exact hmem
    · intro h0
      exact hx0 (hinjE (h0.trans (map_zero R.HE.e).symm))

  have hW' : TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) (R.eWf i (sg0 D A)) SF c ≠ ⊥ := by
    intro hbot
    apply hE'
    apply Submodule.rank_eq_zero.1
    rw [(hTR i).1 c]
    exact Submodule.rank_eq_zero.2 hbot

  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hW'
  obtain ⟨hyF, hyG⟩ := Submodule.mem_inf.1 hy
  have hyR : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrngW]
    exact (Submodule.mem_inf.1 hyG).1
  obtain ⟨z, rfl⟩ := hyR
  refine (Submodule.ne_bot_iff _).2 ⟨z, ?_, ?_⟩
  · show (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) R.triv ⊓ _
    exact Submodule.mem_inf.2 ⟨hyG, hyF⟩
  · rintro rfl
    exact hy0 (map_zero _)

end GlobalTheory.MatchUpProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDense

section Generic

theorem units_tendsto {M ι : Type} [Monoid M] [TopologicalSpace M] {l : Filter ι} {f : ι → Mˣ} {u : Mˣ}
    (h1 : Filter.Tendsto (fun i => (f i : M)) l (nhds (u : M)))
    (h2 : Filter.Tendsto (fun i => (((f i)⁻¹ : Mˣ) : M)) l (nhds ((u⁻¹ : Mˣ) : M))) :
    Filter.Tendsto f l (nhds u) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact h1.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp h2)

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_mul {a b : A} (hab : a * b = 0) (m : Matrix n n A) :
    (a + b) • m + (1 - (a + b)) • (1 : Matrix n n A) =
      (a • m + (1 - a) • (1 : Matrix n n A)) * (b • m + (1 - b) • (1 : Matrix n n A)) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  linear_combination (norm := module) hab • (2 • m - m * m - 1)

omit [Fintype n] in
theorem cut_entry (a : A) (m : Matrix n n A) (i j : n) :
    (a • m + (1 - a) • (1 : Matrix n n A)) i j = a * (m - 1) i j + (1 : Matrix n n A) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

omit [Fintype n] in
theorem cut_supp {a : A} (ha : a * a = a) (m : Matrix n n A) (i j : n) :
    a * (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j = (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j := by
  rw [Matrix.sub_apply, cut_entry, add_sub_cancel_right, ← mul_assoc, ha]

theorem sum_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i, p i * p i = p i)
    (h0 : ∀ i j, i ≠ j → p i * p j = 0) : (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => h0 i j (Ne.symm hji)) (fun hi' => absurd hi hi'), h i]

end Generic

variable {D : D7}

theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε := by
  classical
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1), singleV D.host.F v 1, rfl, ?_, fun w hw => ?_⟩
  · exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
  · exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hw

theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, hα0⟩ := h
  obtain ⟨α', rfl, -, hα0'⟩ := h'
  have hz : α * α' = 0 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α' w = 0
    by_cases hw : w = v
    · have hw' : α' w = 0 := hα0' w (by rw [hw]; exact hv)
      rw [hw', mul_zero]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', zero_mul]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α' = pairA D.host.F (0 * 0) (α * α') from rfl, hz, mul_zero]
  rfl

theorem placeIdem_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε * ε = ε := by
  obtain ⟨α, rfl, hα1, hα0⟩ := h
  have hz : α * α = α := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α w = α w
    by_cases hw : w = v
    · have hw' : α w = 1 := by rw [hw]; exact hα1
      rw [hw', mul_one]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', mul_zero]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α = pairA D.host.F (0 * 0) (α * α) from rfl, hz, mul_zero]

theorem mt_inj (V : HSp D) {g h : GA D V} (e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact e

theorem tendsto_of_mt {ι : Type} {l : Filter ι} (V : HSp D) {f : ι → GA D V} {g : GA D V}
    (h1 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)) l (nhds (Formalism.L2.Theta.mt V g)))
    (h2 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)⁻¹) l (nhds (Formalism.L2.Theta.mt V g⁻¹))) :
    Filter.Tendsto f l (nhds g) := by
  have hind : Topology.IsInducing
      (Subtype.val : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram) → GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Topology.IsInducing.subtypeVal
  exact hind.tendsto_nhds_iff.2 (units_tendsto h1 h2)

theorem infPart_entry (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  have h1 : infHom V g = 1 := (MonoidHom.mem_ker).1 hg
  have h2 := congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1
  simp only [infHom, MonoidHom.comp_apply, Formalism.UG.bc] at h2
  have e1 : infPart D (Formalism.L2.Theta.mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := h2
  have e2 : infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.sub_apply, map_sub, e1, e2, sub_self]

theorem exists_trunc (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v))
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ κ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V → GA D V,
      (∀ g, κ ∅ g = 1) ∧
      (∀ v s (hv : v ∉ s) g, κ (Finset.cons v s hv) g = κ {v} g * κ s g) ∧
      (∀ v g, Stab V β g → Stab V β (κ {v} g) ∧ SuppPl (ε v) V (κ {v} g)) ∧
      ∀ g, Stab V β g → Filter.Tendsto (fun s => κ s g) Filter.atTop (nhds g) := by
  have hid : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)), (∑ v ∈ s, ε v) * (∑ v ∈ s, ε v) = ∑ v ∈ s, ε v :=
    fun s => sum_idem ε s (fun v => placeIdem_idem (hε v)) (fun v w hvw => placeIdem_mul (hε v) (hε w) hvw)
  choose K hK using fun s => GlobalTheory.T.idempotent_twisted_group_endomorphism D V β (∑ v ∈ s, ε v) (hid s)
  have hKm : ∀ s x, Formalism.L2.Theta.mt V (K s x) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) • Formalism.L2.Theta.mt V x +
      (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    fun s x => (hK s x).1
  refine ⟨fun s g => K s g, fun g => ?_, fun v s hv g => ?_, fun v g hg => ⟨(hK {v} g).2 hg, fun i j => ?_⟩, fun g hg => ?_⟩
  · apply mt_inj V
    rw [hKm, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add, GlobalTheory.AdelicLatMove.mt_one]
  · apply mt_inj V
    show Formalism.L2.Theta.mt V (K _ g) = Formalism.L2.Theta.mt V (K {v} g * K s g)
    rw [hKm, GlobalTheory.AdelicLatMove.mt_mul, hKm, hKm, Finset.sum_cons, Finset.sum_singleton, map_add]
    apply cut_mul
    rw [← map_mul, Finset.mul_sum, Finset.sum_eq_zero (fun w hw => placeIdem_mul (hε v) (hε w) (fun hvw => hv (by rw [hvw]; exact hw))), map_zero]
  · show algebraMap (AF D.host.F) (AE D) (ε v) * (Formalism.L2.Theta.mt V (K {v} g) - 1) i j = (Formalism.L2.Theta.mt V (K {v} g) - 1) i j
    rw [hKm, Finset.sum_singleton]
    exact cut_supp (by rw [← map_mul, placeIdem_idem (hε v)]) _ i j
  · have key : ∀ x : GA D V, x ∈ GfC V →
        Filter.Tendsto (fun s => Formalism.L2.Theta.mt V (K s x)) Filter.atTop (nhds (Formalism.L2.Theta.mt V x)) := by
      intro x hx
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      simp only [hKm, cut_entry]
      have hlim := (GlobalTheory.T.tendsto_finitePlaceTruncation_adeleE D ε hε ((Formalism.L2.Theta.mt V x - 1) i j) (infPart_entry V hx i j)).add_const
        ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      have e : (Formalism.L2.Theta.mt V x - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j = Formalism.L2.Theta.mt V x i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [e] at hlim
      exact hlim
    refine tendsto_of_mt V (key g hg.1) ?_
    simpa only [map_inv] using key g⁻¹ (inv_mem hg.1)

theorem mem_of_local (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (H : Subgroup (GA D S × GA D T)) (hH : IsClosed (H : Set (GA D S × GA D T)))
    (hloc : ∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H)
    (g : GA D S) (h : GA D T) (hg : Stab S βS g) (hh : Stab T βT h) : (g, h) ∈ H := by
  choose ε hε using fun v => exists_placeIdem (D := D) v
  obtain ⟨κS, hS0, hSc, hS1, hSt⟩ := exists_trunc ε hε S βS
  obtain ⟨κT, hT0, hTc, hT1, hTt⟩ := exists_trunc ε hε T βT
  have hmem : ∀ s, (κS s g, κT s h) ∈ H := by
    intro s
    induction s using Finset.cons_induction with
    | empty => rw [hS0, hT0]; exact H.one_mem
    | cons v s hv ih =>
      rw [hSc v s hv, hTc v s hv]
      exact H.mul_mem (hloc v (ε v) (hε v) _ _ (hS1 v g hg).1 (hT1 v h hh).1 (hS1 v g hg).2 (hT1 v h hh).2) ih
  exact hH.mem_of_tendsto ((hSt g hg).prodMk_nhds (hTt h hh)) (Filter.Eventually.of_forall hmem)

end GlobalTheory.StabDense

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairAction
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem isBorelU_inv_mixeq {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {g : GU σ n} (hg : IsBorelU g) :
    IsBorelU g⁻¹ := by
  intro i j hij
  exact Formalism.UG.P.spherical_upper_inv (g : GL (Fin n) L) ((Formalism.UG.P.spherical_upper_iff _).1 hg) hij

theorem mixLat_form_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS ℓ hℓ huniq g h hg hh
  have hU := hS.1.unr
  have hnorm : ∀ (g : GU σ n) (h : GU σ n') (x : Matrix (Fin n') (Fin n) L),
      ω (g, h) * ρ x = ρ (h.1.1 * x * ((g.1)⁻¹ : GL (Fin n) L).1) * ω (g, h) := hS.1.norm
  have c1 : ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h →
      ∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v := by
    intro g h hg hh
    refine huniq (ℓ.comp (ω (g, h))) (fun a ha v => ?_)
    have hm := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g⁻¹ h (isBorelU_inv_mixeq hg) hh).1 a ha
    show ℓ (ω (g, h) (ρ a v)) = ℓ (ω (g, h) v)
    rw [← Module.End.mul_apply, hnorm, Module.End.mul_apply]
    exact hℓ _ hm _
  refine ⟨c1 g h hg hh, fun z v => ?_⟩
  obtain ⟨a, ha, ha0, he⟩ := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g h⁻¹ hg (isBorelU_inv_mixeq hh)).2 z
  have key : ρ (embLow n' n z) * ω (g, h) = ω (g, h) * ρ ((h⁻¹).1.1 * embLow n' n z * g.1.1) := by
    rw [hnorm]
    congr 2
    simp [Matrix.mul_assoc]
  set E' := embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1) with hE'
  have h0 : locH σ δ (antiG L n) (antiG L n') a E' = 0 := by
    rw [locH_antiG]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
    by_cases hj : j.1 < n - n / 2
    · rw [ha0 i j hj, zero_mul]
    · rw [hE', embLow, dif_neg (by simp only [Fin.val_rev]; omega), map_zero, mul_zero]
  have hsplit : ρ (a + E') = ρ a * ρ E' := by
    rw [hS.1.rho_mul, h0]
    simp
  rw [← Module.End.mul_apply, key, Module.End.mul_apply, c1 g h hg hh, he, hsplit, Module.End.mul_apply, hℓ a ha]

end GlobalTheory.SphTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquivStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type) [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  first | exact @GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | exact GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | (intros; apply GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit <;> assumption)
end

