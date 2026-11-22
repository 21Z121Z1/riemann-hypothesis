import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLevelSpherical
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopVol

theorem levSph_bT_compact_open : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → levSph W a.g.bT ≤ GfC _ ∧ IsCompact (levSph W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((levSph W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _
  have hx : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ha.top.2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig (I.rec7 l Z).sp.X'.gram
  have hmem : ∀ h, h ∈ levSph W a.g.bT ↔
      a.g.bT⁻¹ * h * a.g.bT ∈ Formalism.IndefR.Lev.levG _ (pk W).βX (datSph W) := fun h => mem_levSph h
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    have h1 : a.g.bT⁻¹ * h * a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ((hmem h).1 hh).1
    have h2 : h = a.g.bT * (a.g.bT⁻¹ * h * a.g.bT) * a.g.bT⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hx h1) (inv_mem hx)
  · have he : (levSph W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) =
        (fun k => a.g.bT * k * a.g.bT⁻¹) '' (Formalism.IndefR.Lev.levG _ (pk W).βX (datSph W) : Set _) := by
      ext h
      constructor
      · intro hh
        exact ⟨_, (hmem h).1 hh, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (hmem _).2 ?_
        have : a.g.bT⁻¹ * (a.g.bT * k * a.g.bT⁻¹) * a.g.bT = k := by group
        rw [this]; exact hk
    rw [he]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _).image (by fun_prop)
  · have ho := GlobalTheory.ParahoricCompact.isOpen_comap_lev _ (pk W).βX (datSph W)
    have hc : Continuous fun k : GfC (I.rec7 l Z).sp.X' => a.g.bT⁻¹ * (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') * a.g.bT := by
      fun_prop
    convert ho.preimage hc using 1
    ext k
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    rw [hmem]
    constructor
    · intro hk; exact hk.2
    · intro hk
      exact ⟨(GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').inv_mem hx) k.2) hx, hk⟩

end GlobalTheory.TopVol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopVol

theorem volLev_ne_zero_of_isCompact {D : D7} (V : HSp D) (hK : IsCompact (GinfC V : Set (GA D V))) (v : GlobalTheory.Unf.Vol V)
    (U : Subgroup (GA D V)) (hle : U ≤ GfC V) (hc : IsCompact (U : Set (GA D V)))
    (ho : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))) : GlobalTheory.SeeSaw.volLev v U ≠ 0 := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hvol : GlobalTheory.SeeSaw.volLev v U = (v.μ K).toReal := by
    unfold GlobalTheory.SeeSaw.volLev
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hc
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho' : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      ho.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho'
    show g ∈ (K : Set (GA D V))
    rw [hKset]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  rw [hvol]
  exact (ENNReal.toReal_pos hKpos.ne' hKfin).ne'

theorem volLev_top_ne_zero : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho
  exact volLev_ne_zero_of_isCompact _
    (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho

end GlobalTheory.TopVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frGL_mul' {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E n y := by
  simp [Formalism.L2.DIV.frGL]

set_option maxHeartbeats 1000000 in

theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : Formalism.IndefR.Lev.EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Formalism.IndefR.Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul' β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem locHom_eq {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) {π' : Formalism.IndefR.Lev.EAf D →+* k}
    (hπ : ∀ a, π' (toEAf D a) = q.pr a) (V : HSp D) (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) (F : GlobalTheory.LocMod.Frame k V.rank Y) (e : Y ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) :
    (GlobalTheory.LevIdx.locHom q V F x).val = (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix e e := by
  have h := mul_moved (ofSplit q) (π' := π') hπ V t x β y hy hM
  have hF : F.β = (F.β.submatrix id e.symm).submatrix id e := by
    ext i j; simp
  rw [GlobalTheory.LevIdx.locHom_val]
  generalize (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) = Yn at h ⊢
  generalize hMm : F.β.submatrix id e.symm = Mm at h hF
  have key : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) k) (B : Matrix (Fin V.rank) (Fin V.rank) k),
      A * B.submatrix id e = (A * B).submatrix id e := fun A B => by
    ext i j; simp [Matrix.mul_apply]
  have h' : (mt V x).map q.pr * Mm = Mm * Yn := h
  have h2 : (mt V x).map q.pr * F.β = F.β * Yn.submatrix e e := by
    calc (mt V x).map q.pr * F.β = (mt V x).map q.pr * Mm.submatrix id e := by rw [← hF]
      _ = ((mt V x).map q.pr * Mm).submatrix id e := key _ _
      _ = (Mm * Yn).submatrix id e := by rw [h']
      _ = Mm.submatrix id e * Yn.submatrix e e := (Matrix.submatrix_mul_equiv Mm Yn id e e).symm
      _ = F.β * Yn.submatrix e e := by rw [← hF]
  calc F.γ * (mt V x).map q.pr * F.β = F.γ * ((mt V x).map q.pr * F.β) := Matrix.mul_assoc _ _ _
    _ = F.γ * (F.β * Yn.submatrix e e) := by rw [h2]
    _ = Yn.submatrix e e := by rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_twist_levTop {s : ℕ} {τ κ : Type} [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ)
    (hδ : GlobalTheory.SplitWeil.IsTame δ) (ν : ℕ → kˣ →* ℂˣ) (x : GL (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2)) k) :
    x ∈ (GlobalTheory.StepData.twistChain s τ κ δ hδ ν).levTop.J ↔
      x ∈ GlobalTheory.SplitWeil.KO k _ ∧ ∀ i j, ValuativeRel.valuation k (x.val (Sum.inr i) (Sum.inl j)) < 1 := by
  have e : (GlobalTheory.StepData.LatFrame.refl k (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2))).conj.symm x = x := by
    rw [MulEquiv.symm_apply_eq]
    ext i j
    simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_val]
  show x ∈ ((GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 2) × τ) δ hδ).toLevel.map
    (GlobalTheory.StepData.LatFrame.refl k _).conj).J ↔ _
  rw [GlobalTheory.StepData.Level.mem_map, e, GlobalTheory.StepData.mem_parahoric]
  rfl

theorem frGL_inv {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {t g : GA D V}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) :
    Formalism.L2.DIV.frGL β y⁻¹ = Formalism.IndefR.Lev.finE V (t⁻¹ * g⁻¹ * t) := by
  have e : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
  exact ((Formalism.L2.DIV.frGL β).map_inv y).trans ((congrArg (·⁻¹) hy).trans
    (((Formalism.IndefR.Lev.finE V).map_inv _).symm.trans (congrArg (Formalism.IndefR.Lev.finE V) e.symm)))

set_option maxHeartbeats 1000000 in

theorem red_iff {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] (q : SplitPt D k)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (t g : GA D V)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (F : GlobalTheory.LocMod.Frame k V.rank (R ⊕ S)) (e : R ⊕ S ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) (r : ℕ)
    (hl : ∀ a, (e (Sum.inl a)).val < r) (hr : ∀ a, r ≤ (e (Sum.inr a)).val)
    (hst : Formalism.IndefR.Lev.finE V (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) ∈ blockTri (blk2 r) ↔
      GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ ∧
        ∀ i j, ValuativeRel.valuation k ((GlobalTheory.LevIdx.locHom q V F g).val (Sum.inr i) (Sum.inl j)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hPP
  obtain ⟨y, hy⟩ := hst
  have h1 := locHom_eq q hπ V t g β y hy F e hM
  have h2 := locHom_eq q hπ V t g⁻¹ β y⁻¹ (frGL_inv hy) F e hM
  have hK : GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [h1]; exact hred.int _
    · rw [← (GlobalTheory.LevIdx.locHom q V F).map_inv, h2]; exact hred.int _
  have h3 : Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (Formalism.L2.DIV.redFn β PP) hy.symm).trans (redFn_frGL β PP y)
  rw [h3, mem_blockTri, h1]
  constructor
  · intro h
    refine ⟨hK, fun i j => (hred.ker _).1 (h (e (Sum.inr i)) (e (Sum.inl j)) ?_)⟩
    simp [blk2, hl j, (hr i).not_gt]
  · rintro ⟨-, h⟩ i j hij
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i
    · simp [blk2, hl i] at hij
    rcases j with j | j
    · exact (hred.ker _).2 (h i j)
    · simp [blk2, (hr i).not_gt, (hr j).not_gt] at hij

set_option maxHeartbeats 1000000 in

theorem red_iff_levTop {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP)
    (δ : G.kˣ →* ℂˣ) (hδ : GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) (g : GA D c.T)
    (hst : Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT) ∈ Formalism.L2.DIV.St B.βT) :
    Formalism.L2.DIV.redFn B.βT PP (Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ x, (mt c.T g).map G.q.pr = G.FT.β * Units.val x * G.FT.γ → x ∈ (G.T δ hδ η).levTop.J := by
  obtain ⟨e, he, hM⟩ := G.frameTop
  have hs := G.hs
  have hk : D.R.r = D.R.k + (G.s + 1) := by
    unfold Ranks.r
    omega
  refine (red_iff G.q PP G.idem c.T B.bT g B.βT G.FT e hM _ (fun a => ?_) (fun a => ?_) hst).trans ?_
  · rw [he, hk]
    rcases a with a | a
    · exact lt_of_lt_of_le a.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left a.2 _
  · rw [he, hk]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · refine (mem_twist_levTop δ hδ η _).symm.trans ⟨fun h x hx => ?_, fun h => h _ ?_⟩
    · obtain rfl := (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g x).1 hx
      exact h
    · exact (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g _).2 rfl

theorem levS_split (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) (κ : GA D V) :
    κ ∈ levS V β L ↔ κ ∈ levS V β { L with Q := ∅, xq := ξ } ∧
      ∀ PP ∈ L.Q, Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V κ) ∈ blockTri (blk2 L.r) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, b, c, d⟩ := mem_parLev.1 h2
    exact ⟨⟨h1, mem_parLev.2 ⟨a, b, c, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, h3⟩, d⟩
  · rintro ⟨⟨h1, h2, h3⟩, d⟩
    obtain ⟨a, b, c, -⟩ := mem_parLev.1 h2
    exact ⟨h1, mem_parLev.2 ⟨a, b, c, d⟩, h3⟩

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree

set_option maxHeartbeats 1000000 in

theorem main : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (J : QJ a t), J.Reads → ∀ g, g ∈ levTw W a.g.bT t ↔ g ∈ levSph W a.g.bT ∧ ∀ i x, (mt (I.rec7 l Z).sp.X' g).map (J.G i).q.pr = (J.G i).FT.β * Units.val x * (J.G i).FT.γ → x ∈ ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).levTop.J := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ t J hJ g
  refine (mem_levTw g).trans ((levS_split _ (pk W).βX (datXP (pk W) (lvP W) t) (datSph W).xq _).trans
    ((and_congr_right fun hS => ?_).trans (and_congr_left fun _ => (mem_levSph g).symm)))
  have key := fun i => red_iff_levTop (J.G i) (J.E i).δ (J.E i).tame (J.E i).η g (parLev_St hS.2.1)
  constructor
  · exact fun h i => (key i).1 (h _ (J.mem i))
  · intro h PP hP
    obtain ⟨i, rfl⟩ := hJ.surj PP hP
    exact (key i).2 (h i)

end GlobalTheory.TopAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.TwistPlaces

theorem sel_under {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hsel : Formalism.L2.Col.IsSel X sel) {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {P : HeightOneSpectrum (𝓞 X.E)}
    (h : P ∈ Formalism.L2.Col.QE sel ξ) : sel (P.under (𝓞 X.F)) = P := by
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    have e : (sel v).under (𝓞 X.F) = v := HeightOneSpectrum.ext (hsel v)
    rw [e]
  · exact absurd h (Finset.notMem_empty _)

theorem places_injective : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (J : QJ a t), J.Reads → Function.Injective fun i => (J.G i).q.v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ i i' hv
  have hv : (J.G i).q.v = (J.G i').q.v := hv
  have und : ∀ n, (J.pl n).under (𝓞 (I.rec7 l Z).host.F) = (J.G n).q.v := fun n => by
    obtain ⟨ε, hε, hε'⟩ := (J.G n).q.above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G n).idem hε hε'
  have hs : ∀ n, I.sel (J.G n).q.v = J.pl n := fun n => by
    rw [← und n]
    exact sel_under hW.tr.ok.sel_ok ((hW.tq.Q t _).1 (J.mem n))
  apply hJ.inj
  rw [← hs i, ← hs i', hv]

end GlobalTheory.TopVol.TwistPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.JoinFrames

theorem movedAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ i, MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i) :=
  fun W hW u a ha _ t J hJ i => GlobalTheory.Fam.QJ.Reads.movedAt W hW u a ha t J hJ i

end GlobalTheory.QTw.JoinFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.QJPlaces

theorem places_under : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads →
    Function.Injective (fun i => (J.G i).q.v) ∧ ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ
  have hund : ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
    intro i
    obtain ⟨ε, hε, he⟩ := (J.G i).q.above
    exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε he).symm
  refine ⟨fun i j hij => ?_, hund⟩
  have h1 : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.pl j).under (𝓞 (I.rec7 l Z).host.F) := by
    have := hij
    simp only at this
    rw [hund i, hund j] at this
    exact this
  exact hJ.inj (hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t, J.mem j⟩ h1)

end GlobalTheory.Fam.QJPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.FinData

theorem isFinComb_smul {D : D7} {S T : HSp D} (r : ℂ) (c : WO S T →₀ ℂ) (h : GlobalTheory.SeeSaw.IsFinComb c) :
    GlobalTheory.SeeSaw.IsFinComb (r • c) := fun u hu => h u (Finsupp.support_smul hu)

theorem main : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ t J _ s j α γ hj
  refine ⟨?_, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atG j).2.1, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atT j).1⟩
  unfold QJ.dQ
  refine isFinComb_smul _ _ (isFinComb_smul _ _ (GlobalTheory.QPl.ThetaPin.isFinComb_aconv _ fun e he => ?_))
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨ε, hε, hsum⟩ := (J.G i).q.above
  have hs := (J.G i).hs
  refine GlobalTheory.QPl.ThetaPin.isFinComb_of_half hε _ fun w hw => hsum ▸ ?_
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  rcases Nat.lt_or_ge j (J.G i).s with h1 | h1
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = (J.G i).s := ⟨(J.G i).s - j - 1, by omega⟩
    exact ((J.E i).dL_mid j d hd (α i) (γ i)).1 w hw
  · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2
      exact ((J.E i).dL_pen (α i) (γ i)).1 w hw
    · obtain rfl : j = (J.G i).s + 1 := by omega
      exact ((J.E i).dL_top (α i) (γ i)).1 w hw

end GlobalTheory.Fam.FinData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_quadratic_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∃ e₀ : AE (I.rec7 l Z), IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs) ∧ J.A.e = e₀ + ∑ i, (J.G i).q.e := by
  first | exact @GlobalTheory.Fam.IdemSplitTw.idem_eq_add_twist | exact GlobalTheory.Fam.IdemSplitTw.idem_eq_add_twist | (intros; apply GlobalTheory.Fam.IdemSplitTw.idem_eq_add_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam

theorem xi_eq_xiOff_mul_join : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) α γ z, J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z = xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ j hj α γ z
  rw [(GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local I hW.tr.ok hW.tr.tw l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is).1 j hj (J.ι j α) (J.ι (j + 1) γ) z]
  congr 1
  symm
  refine Finset.prod_bij (fun i _ => J.P i) ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hJ.eq i]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    exact Finset.disjoint_left.1 ((GlobalTheory.PkPlaces.pk_places W hW.pk).2 t).1 ((hW.lev.2.1 _).2 h) (J.mem i)
  · intro i₁ _ i₂ _ h
    exact hJ.inj (((hJ.eq i₁).symm.trans (congrArg Subtype.val h)).trans (hJ.eq i₂))
  · intro P hP
    have hv : P.1 ∉ (B.primes X).vGs := (Finset.mem_filter.1 hP).2
    have hq : P.1 ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact absurd h hv
      · exact h
    obtain ⟨i, hi⟩ := hJ.surj _ ((hW.tq.Q t P.1).2 hq)
    exact ⟨i, Finset.mem_univ _, Subtype.ext ((hJ.eq i).trans hi)⟩
  · intro i _
    rfl

end GlobalTheory.Fam
end

