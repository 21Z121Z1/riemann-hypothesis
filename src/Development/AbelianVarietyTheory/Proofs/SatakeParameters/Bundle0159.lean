import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealPointsToUnitaryGroupVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0009
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLiftTwistedModelIffUntwisted
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open Formalism.L2.Col
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.HeckeLifts₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

abbrev SysL (A3 : FamIn3 K G Pl0 I0 Ty T m) (j : Fin m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

end Abstract

section TwEig

variable {s : Bool} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_map_mul (a b : Module.End ℂ E) : (Tw.map s (a * b) : Module.End ℂ (Tw s E)) = Tw.map s a * Tw.map s b :=
  LinearMap.ext fun _ => rfl

theorem tw_map_pow (a : Module.End ℂ E) (k : ℕ) : (Tw.map s (a ^ k) : Module.End ℂ (Tw s E)) = Tw.map s a ^ k := by
  induction k with
  | zero => exact LinearMap.ext fun _ => rfl
  | succ k ih => rw [pow_succ, tw_map_mul, ih, pow_succ]

theorem tw_map_sub_smul (a : Module.End ℂ E) (μ : ℂ) :
    (Tw.map s a - μ • 1 : Module.End ℂ (Tw s E)) = Tw.map s (a - cj s μ • 1) :=
  LinearMap.ext fun _ => rfl

theorem mem_maxGen_tw (a : Module.End ℂ E) (μ : ℂ) (v : Tw s E) :
    v ∈ Module.End.maxGenEigenspace (Tw.map s a : Module.End ℂ (Tw s E)) μ ↔ Tw.out v ∈ a.maxGenEigenspace (cj s μ) := by
  simp only [Module.End.mem_maxGenEigenspace]
  rw [tw_map_sub_smul]
  refine exists_congr fun k => ?_
  rw [← tw_map_pow]
  exact Iff.rfl

theorem eigAt_tw {I : Type} (h : I → Module.End ℂ E) (y : I → ℂ) :
    eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) y = Tw.sub s (eigAt h fun i => cj s (y i)) := by
  refine SetLike.ext fun v => ?_
  rw [show v ∈ Tw.sub s (eigAt h fun i => cj s (y i)) ↔ Tw.out v ∈ eigAt h (fun i => cj s (y i)) from Iff.rfl]
  simp only [eigAt, Submodule.mem_iInf]
  exact forall_congr' fun i => mem_maxGen_tw (h i) (y i) v

theorem sub_iSup {ι : Type} (V : ι → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun c v hv => (le_iSup V c) hv)
  exact Submodule.iSup_induction V (motive := fun y => (Tw.mk s y : Tw s E) ∈ ⨆ c, Tw.sub s (V c)) hx
    (fun c y hy => Submodule.mem_iSup_of_mem c hy) (zero_mem _) (fun a b ha hb => add_mem ha hb)

theorem sub_iSup_prop {P : Prop} (V : P → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  by_cases hP : P
  · rw [iSup_pos hP, iSup_pos hP]
  · rw [iSup_neg hP, iSup_neg hP]
    rfl

theorem eigSum_tw {I : Type} (h : I → Module.End ℂ E) (Q : (I → ℂ) → Prop) :
    eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (eigSum h fun x => Q fun i => cj s (x i)) := by
  unfold eigSum
  rw [sub_iSup]
  simp only [sub_iSup_prop, eigAt_tw]
  have hcc : ∀ y : I → ℂ, (fun i => cj s (cj s (y i))) = y := fun y => funext fun i => cj_cj s (y i)
  refine le_antisymm (iSup₂_le fun y hy => le_iSup₂_of_le (fun i => cj s (y i)) (by rw [hcc]; exact hy) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (fun i => cj s (x i)) hx ?_)
  rw [hcc]

end TwEig

section Concrete

open HeckeLiftsCompare

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def twE (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Module.End ℂ ((R.toCx3 F).W j) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H : Module.End ℂ (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H))

theorem theta_jL (j : Fin D.R.m) (t : T) (y : (A3.A.fam.L j t).S.Forms) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t y) =
      (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (R.jV j t y)) :
        Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) := rfl

theorem twE_smul (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) (c : ℂ) (v : (R.HW j (sg0 D A3.A)).H) :
    twE R F j H (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) v : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) =
      (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) (H v) : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H).map_smul c _

theorem intw_of_rat (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)))
    (u : (R.toCx3 F).FLC j t) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have key : ((R.toCx3 F).θ' j t) ∘ₗ ((R.toCx3 F).opLC j t (Sum.inl i)) = (twE R F j H) ∘ₗ ((R.toCx3 F).θ' j t) := by
    refine LinearMap.ext_on (hK j t).2 ?_
    rintro _ ⟨k, rfl⟩
    have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) (CxData.bL (A := A3.fam3.amb3) j t k)
    simp only [LinearMap.comp_apply]
    refine (congrArg ((R.toCx3 F).θ' j t) e1.symm).trans ?_
    refine (theta_jL j t _).trans ?_
    refine Eq.trans ?_ (congrArg (twE R F j H) (theta_jL j t _).symm)
    refine Eq.trans ?_ (twE_smul j H _ _).symm
    exact congrArg (fun v => (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) v :
      Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H)) (h _)
  exact LinearMap.congr_fun key u

open Classical in

def spOf (hW' : IndefiniteRowSideFullHecke.LocalHeckeLifts.OpW R.toRealDat) (j : Fin D.R.m) (t : T) (i : A3.A.ok t × ℕ) : Module.End ℂ (R.HW j (sg0 D A3.A)).H :=
  if i.2 ≤ (Vc D j).rank then hW' j t (Sum.inl i) else 0

abbrev SysC (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys D.what₂.embLL ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

theorem sysL_cj (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) (x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) :
    SysL A3 j p (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) ↔ SysC A3 j p x := by
  constructor
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i) := congrFun hy.2 i
    rw [R.toRealDat.emb0] at e
    rw [← cj_cj (twAt D.what₂.embLL A3.A.v0) (x i), e, cj_cj]
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : x i = D.what₂.embLL (y i) := congrFun hy.2 i
    show cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i)
    rw [R.toRealDat.emb0, e]

def unE (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : Module.End ℂ (Tw s E)) : Module.End ℂ E where
  toFun v := Tw.out (h (Tw.mk s v))
  map_add' x y := (congrArg Tw.out (h.map_add (Tw.mk s x) (Tw.mk s y)))
  map_smul' c v := by
    have e : (Tw.mk s (c • v) : Tw s E) = cj s c • Tw.mk s v := by
      show c • v = cj s (cj s c) • v
      rw [cj_cj]
    show Tw.out (h (Tw.mk s (c • v))) = c • Tw.out (h (Tw.mk s v))
    rw [e, map_smul, Tw.out_smul, cj_cj]

theorem twE_commute (j : Fin D.R.m) (a b : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Commute (twE R F j a) (twE R F j b) ↔ Commute a b :=
  ⟨fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v, fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v⟩

theorem rat_of_intw (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (hph : R.phs j ≠ 0) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ u, (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u))
    (f : (A3.A.fam.L j t).S.Forms) :
    R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) f
  have e2 := (congrArg ((R.toCx3 F).θ' j t) e1).trans (h _)
  have e3 := ((theta_jL (R := R) (F := F) j t _).symm.trans e2).trans
    ((congrArg (twE R F j H) (theta_jL j t f)).trans (twE_smul j H _ _))
  exact smul_right_injective (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) hph e3

structure UntwL (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) : Prop where
  rat : ∀ j t i f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = g j t i (R.thG j t (R.jV j t f))
  comm : ∀ j, PairComm (g j A3.A.fam.μ0)
  parts : ∀ j p, R.Wp3 j p = eigSum (g j A3.A.fam.μ0) (SysC A3 j p)

theorem sub_inj (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A B : Submodule ℂ E}
    (h : Tw.sub s A = Tw.sub s B) : A = B :=
  SetLike.ext fun x => SetLike.ext_iff.1 h (Tw.mk s x)

theorem hecke_theta_lift_twisted_model_iff_untwisted (hM : R.toRealDat.IsModels) (hph : ∀ j, R.phs j ≠ 0)
    (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    HeckeIntertwiningLifts A3 (R.toCx3 F) (fun j t i => twE R F j (g j t i)) ↔ UntwL (R := R) g := by
  have hp : ∀ j p, eigSum (fun i => twE R F j (g j A3.A.fam.μ0 i)) (SysL A3 j p) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0) (eigSum (g j A3.A.fam.μ0) (SysC A3 j p)) := fun j p => by
    have e := eigSum_tw (s := twAt D.what₂.embLL A3.A.v0) (g j A3.A.fam.μ0) (SysL A3 j p)
    have e' : (fun x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ => SysL A3 j p fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) =
        SysC A3 j p := funext fun x => propext (sysL_cj R j p x)
    rw [e'] at e
    exact e
  constructor
  · intro h
    refine ⟨fun j t i f => rat_of_intw hM j (hph j) t i _ (h.intw j t i) f, fun j i i' => (twE_commute j _ _).1 (h.comm j i i'), fun j p => ?_⟩
    refine sub_inj (twAt D.what₂.embLL A3.A.v0) ?_
    exact (h.parts j p).trans (hp j p)
  · intro h
    refine ⟨fun j t i u => intw_of_rat hM j t i _ (h.rat j t i) u, fun j i i' => (twE_commute j _ _).2 (h.comm j i i'), fun j p => ?_⟩
    refine Eq.trans ?_ (hp j p).symm
    exact congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (h.parts j p)

theorem phs_ne_zero (hC : R.WeakCharacterisation F) (j : Fin D.R.m) : R.phs j ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [(hC.phase j).1]; exact one_ne_zero)

def unW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (h : Module.End ℂ ((R.toCx3 F).W j)) :
    Module.End ℂ (R.HW j (sg0 D A3.A)).H :=
  unE (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) h

theorem untw_of_hH (hC : R.WeakCharacterisation F) {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ ((R.toCx3 F).W j)}
    (hH : HeckeIntertwiningLifts A3 (R.toCx3 F) hW) : UntwL (R := R) fun j t i => unW R F j (hW j t i) :=
  (hecke_theta_lift_twisted_model_iff_untwisted (F := F) hC.base.models (phs_ne_zero hC) fun j t i => unW R F j (hW j t i)).1 hH

end Concrete

end GlobalTheory.HeckeLifts₂

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HopfOrderScalarExtension
section
open NumberField GlobalTheory.LKTrip GlobalTheory.HTBetti GlobalTheory.Kg
open scoped TensorProduct Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

def extZero (s : Fin n → Prop) [DecidablePred s] : ({i // s i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w i := if hi : s i then w ⟨i, hi⟩ else 0
  map_add' a b := by funext i; by_cases hi : s i <;> simp [hi]
  map_smul' r a := by funext i; by_cases hi : s i <;> simp [hi]

theorem extZero_apply_mem (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) (i : {i // s i}) :
    extZero s w i = w i := by simp [extZero, i.2]

theorem extZero_apply_not (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) {i : Fin n} (hi : ¬ s i) :
    extZero s w i = 0 := by simp [extZero, hi]

theorem quad_mulVec (h X : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    star (X *ᵥ u) ⬝ᵥ h *ᵥ (X *ᵥ u) = star u ⬝ᵥ (Xᴴ * h * X) *ᵥ u := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem re_quad_ext (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (s : Fin n → Prop) [DecidablePred s]
    (w : {i // s i} → ℂ) :
    (star ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w) ⬝ᵥ
        h *ᵥ ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w)).re =
      ∑ i, hh.eigenvalues i * Complex.normSq (extZero s w i) := by
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp hh.eigenvectorUnitary.2, Matrix.one_mulVec]

theorem finrank_le_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ u ∈ S, u ≠ 0 → 0 < (star u ⬝ᵥ h *ᵥ u).re) :
    Module.finrank ℂ S ≤ Fintype.card {i : Fin n // 0 < hh.eigenvalues i} := by
  refine GlobalTheory.SylvesterInertia.finrank_le_card_of_vanish
    (star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) S _ fun u hu hv => ?_
  by_contra hne
  have hpos := hS u hu hne
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh u] at hpos
  refine absurd hpos (not_lt.mpr (Finset.sum_nonpos fun i _ => ?_))
  by_cases hi : 0 < hh.eigenvalues i
  · rw [hv i hi, map_zero, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (Complex.normSq_nonneg _)

end GlobalTheory.SimSign

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

def phi (h X : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (s : Fin n → Prop) [DecidablePred s] :
    ({i // s i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.mulVecLin X ∘ₗ Matrix.mulVecLin (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∘ₗ extZero s

theorem sum_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (w : {i // 0 < hh.eigenvalues i} → ℂ)
    (hw : w ≠ 0) : 0 < ∑ i, hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i ≤ hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    intro i _
    by_cases hi : 0 < hh.eigenvalues i
    · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
    · rw [extZero_apply_not _ w hi]; simp
  have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i < hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    refine ⟨j.1, Finset.mem_univ _, ?_⟩
    rw [extZero_apply_mem]
    exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
  simpa using Finset.sum_lt_sum hle hlt

end GlobalTheory.SimSign

namespace GlobalTheory.HTBetti

end GlobalTheory.HTBetti

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Hk3

theorem inertJunk_iff {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {m : ℕ}
    (A3 : FamIn3 K G Pl0 I0 (List ℕ) T m) :
    InertJunk A3 ↔
      ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨
          ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧
        ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨
          ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) :=
  ⟨fun h => ⟨fun t k => h.R t k.1 k.2, fun j t k => h.L j t k.1 k.2⟩,
    fun h => ⟨fun t Q s => h.1 t (Q, s), fun j t Q s => h.2 j t (Q, s)⟩⟩

theorem inertJunk_colIn3 {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    InertJunk (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) :=
  FamModel.inertJunk_col W Ch sel hX v0 TU Xg S0 xiVal trIv

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximal
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ringHomConjTranspose_mul_rev (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem sigmaConjTranspose_integral_gramSeparation (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  show Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact hA j i

theorem val_div_pow_le_one {ϖ x y : L} {k m : ℕ} (hϖ : Valued.v ϖ ≤ 1) (hy : Valued.v y = Valued.v ϖ) (hϖ0 : ϖ ≠ 0)
    (hx : Valued.v x ≤ Valued.v ϖ ^ m) (hkm : k ≤ m) : x * (y ^ k)⁻¹ ∈ Formalism.UG.intL L := by
  show Valued.v (x * (y ^ k)⁻¹) ≤ 1
  have h0 : Valued.v ϖ ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hϖ0)
  have h1 : Valued.v x ≤ Valued.v ϖ ^ k := hx.trans (pow_le_pow_right_of_le_one' hϖ hkm)
  rw [map_mul, map_inv₀, map_pow, hy]
  calc Valued.v x * (Valued.v ϖ ^ k)⁻¹ ≤ Valued.v ϖ ^ k * (Valued.v ϖ ^ k)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ h0

end GlobalTheory.Hk3.GramSep

namespace GlobalTheory.Hk3.GramSep

theorem eint : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  intro L _ _ ϖ σ hvϖ hv n r JS a M e Γ hJS hSD he hM haM hΓ
  classical
  have hΓv : ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j) := hΓ.2
  have hϖlt : Valued.v ϖ < 1 := by
    rw [hvϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]; decide
  have hϖ1 : Valued.v ϖ ≤ 1 := hϖlt.le
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hσϖ0 : σ ϖ ≠ 0 := (map_ne_zero σ).mpr hϖ0
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJ
  set D : Matrix (Fin r) (Fin r) L := diagonal fun k => ϖ ^ e k with hD
  set Di : Matrix (Fin r) (Fin r) L := diagonal fun k => (ϖ ^ e k)⁻¹ with hDi
  set Ds : Matrix (Fin r) (Fin r) L := diagonal fun k => σ ϖ ^ e k with hDs
  set Dsi : Matrix (Fin r) (Fin r) L := diagonal fun k => (σ ϖ ^ e k)⁻¹ with hDsi
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
  have hDsiDs : Dsi * Ds = 1 := by
    rw [hDs, hDsi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact inv_mul_cancel₀ (pow_ne_zero _ hσϖ0)
  have hcTD : Formalism.UG.cT σ D = Ds := by
    rw [hD, hDs]; unfold Formalism.UG.cT
    rw [diagonal_map (map_zero σ), diagonal_transpose]
    congr 1; funext k; simp
  have haia : ai * A = 1 := by rw [hai, hA]; exact a.inv_mul
  have hcTa : Formalism.UG.cT σ ai * Formalism.UG.cT σ A = 1 := by
    have haai : A * ai = 1 := by rw [hai, hA]; exact a.mul_inv
    rw [← ringHomConjTranspose_mul_rev, haai]
    unfold Formalism.UG.cT; rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

  set P : Matrix (Fin n) (Fin r) L := ai * M * D with hP
  have hPi : ∀ i k, P i k ∈ Formalism.UG.intL L := by
    intro i k; rw [hP, hD, mul_diagonal]; exact haM i k
  set G1 : Matrix (Fin r) (Fin r) L := Di * Γ with hG1
  have hG1i : ∀ k j, G1 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG1, hDi, diagonal_mul, mul_comm]
    exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) (le_max_left _ _)
  set G2 : Matrix (Fin r) (Fin r) L := Γ * Dsi with hG2
  have hG2i : ∀ k j, G2 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG2, hDsi, mul_diagonal]
    exact val_div_pow_le_one hϖ1 (hv ϖ) hϖ0 (hΓv k j) (le_max_right _ _)
  have hcTM := sigmaConjTranspose_integral_gramSeparation σ hv hM
  have hSDa : ∀ i j, (Formalism.UG.cT σ A * J * A) i j ∈ Formalism.UG.intL L := hSD.1
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have e1 : ai * (M * Γ * Formalism.UG.cT σ M * J) = P * G1 * (Formalism.UG.cT σ M * J) := by
      rw [hP, hG1]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]
    rw [e1]
    exact matMul_int (matMul_int hPi hG1i) (matMul_int hcTM hJS) i j
  · have e2 : M * Γ * Formalism.UG.cT σ M * J * A = M * G2 * (Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A)) := by
      rw [hP, hG2, ringHomConjTranspose_mul_rev, ringHomConjTranspose_mul_rev, hcTD]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Dsi Ds, hDsiDs, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.cT σ ai) (Formalism.UG.cT σ A), hcTa,
        Matrix.one_mul]
    rw [e2]
    exact matMul_int (matMul_int hM hG2i) (matMul_int (sigmaConjTranspose_integral_gramSeparation σ hv hPi) hSDa) i j
  · set G3 : Matrix (Fin r) (Fin r) L := Matrix.of fun k j => Γ k j * (ϖ ^ 1)⁻¹ with hG3
    have hG3i : ∀ k j, G3 k j ∈ Formalism.UG.intL L := by
      intro k j
      exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) ((he k).trans (le_max_left _ _))
    have hΓ3 : Γ = ϖ • G3 := by
      ext k j; rw [hG3]; simp only [Matrix.smul_apply, of_apply, smul_eq_mul, pow_one]
      field_simp
    have e3 : M * Γ * Formalism.UG.cT σ M * J = ϖ • (M * G3 * Formalism.UG.cT σ M * J) := by
      rw [hΓ3, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    rw [e3, Matrix.smul_apply, smul_eq_mul, map_mul]
    have hint : Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ 1 :=
      matMul_int (matMul_int (matMul_int hM hG3i) hcTM) hJS i j
    calc Valued.v ϖ * Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hϖlt

end GlobalTheory.Hk3.GramSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
section
open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryUnramifiedUnit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

namespace GlobalTheory.KerJ

theorem unUnit_of_mtType : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ u μ, MtType u (t.O u μ).mt) → t.ent.UnUnit := by
  intro D L hT Gi Gl K Y cX ex t hm u μ w hw i hi c c'
  have h3 := GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType D u (D.chTw u μ) _ (hm u μ)
  have hb := CharVal.brRho_holds D _ _ h3
  rw [t.kf_un u μ w hw i hi c c']
  exact (t.kf u μ w hw).norm_un ((t.kf u μ w hw).unUnit_of t.idl t.idl_ok hb (GlobalTheory.T.kernelBasis_determinant_abs_at_place _ _ _ _ _ _ _ _ _)) hi c c'

end GlobalTheory.KerJ
end

