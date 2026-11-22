import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0412
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinPl.PutIn.Factor

variable {D : D7}

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

theorem isSBHalf_of_half_eq {S T : HSp D} {b : AE D} {Λ Λ' : AddSubgroup (WO S T)} {Ψ : WO S T → ℂ}
    (hΛ : ∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) (hΨ : IsSBHalf b Λ' Ψ) : IsSBHalf b Λ Ψ := by
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := hΨ
  refine ⟨hsupp, k, hk, fun u hu hub t => hinv u ((hΛ u hub).2 hu) hub t, fun t ht => ?_⟩
  exact (hΛ _ (half_nsmul (hsupp t ht) k)).1 (hfin t ht)

theorem half_smul_self {m n : ℕ} {b : AE D} {x : Mx D m n} (hx : IsHalf b x) : b • x = x := by
  ext i j; exact hx i j

theorem half_of_idem {m n : ℕ} {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem isSBHalf_tens {S T : HSp D} {a b : AE D} {Λ : AddSubgroup (WO S T)} {Φ Ψ : WO S T → ℂ}
    (hab : a * b = 0) (hb : b * b = b) (hbΛ : ∀ u ∈ Λ, b • u ∈ Λ) (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) :
    IsSBHalf (a + b) Λ (tens b Φ Ψ) := by
  obtain ⟨sΦ, kΦ, hkΦ, iΦ, fΦ⟩ := hΦ
  obtain ⟨sΨ, kΨ, hkΨ, iΨ, fΨ⟩ := hΨ
  have hne : ∀ t, tens b Φ Ψ t ≠ 0 → Φ (t - b • t) ≠ 0 ∧ Ψ (b • t) ≠ 0 := fun t ht => by
    rw [tens_apply] at ht
    exact ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, fun u hu hua t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hne t ht
    intro i j
    have h := sΦ _ h1 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    linear_combination h + (t i j) * hab
  · have hbu : b • u ∈ Λ := hbΛ u hu
    have hsub : u - b • u ∈ Λ := Λ.sub_mem hu hbu
    have hau : IsHalf a (u - b • u) := fun i j => by
      have e1 := hua i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination e1 - (u i j) * hab - (u i j) * hb + (u i j) * hb
    have hA : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    have hB : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [tens_apply, tens_apply, hA, hB,
      iΦ _ (AddSubgroup.nsmul_mem Λ hsub kΨ) (half_nsmul hau kΨ),
      iΨ _ (AddSubgroup.nsmul_mem Λ hbu kΦ) (half_nsmul (half_of_idem hb u) kΦ)]
  · obtain ⟨h1, h2⟩ := hne t ht
    have hC : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hC]
    exact Λ.add_mem (AddSubgroup.nsmul_mem Λ (fΦ _ h1) kΨ) (AddSubgroup.nsmul_mem Λ (fΨ _ h2) kΦ)

open GlobalTheory.LocMod.TensorModel in

theorem isPlaceModel_tensR : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  intro D ψ S T a b Λ Λ' Φ f₀ Tm hab hb hbΛ hΛ hΦ hP
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => Ψ (t + x)) = fun t => tens b Φ Ψ (t + x) := by
      funext t
      simp only [tens_apply]
      rw [smul_add, half_smul_self hx, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.trans _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') x (half_sum hab hx)
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
      funext t
      simp only [tens_apply]
      by_cases h0 : Φ (t - b • t) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero hab (hΦ.1 _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.modul _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') y (half_sum_cA hab hy)
  · have hind : halfInd b Λ' = halfInd b Λ := by
      funext t
      unfold halfInd
      have hiff : (t ∈ Λ' ∧ IsHalf b t) ↔ (t ∈ Λ ∧ IsHalf b t) :=
        ⟨fun h => ⟨(hΛ t h.2).1 h.1, h.2⟩, fun h => ⟨(hΛ t h.2).2 h.1, h.2⟩⟩
      by_cases h : t ∈ Λ ∧ IsHalf b t
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (mt hiff.1 h), if_neg h]
    rw [one_smul, hind]
    rfl

end GlobalTheory.FinPl.PutIn.Factor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllBij

section Comb

variable {G : Type} [Group G]

def act (c : G →₀ ℂ) (F : G → ℂ) : G → ℂ := c.sum fun g x => x • rTrans g F

theorem act_apply (c : G →₀ ℂ) (F : G → ℂ) (y : G) : act c F y = c.sum fun g x => x * F (y * g) := by
  simp [act, Finsupp.sum, Finset.sum_apply, rTrans]

def cmul (c d : G →₀ ℂ) : G →₀ ℂ := c.sum fun g x => d.sum fun h y => Finsupp.single (g * h) (x * y)

theorem act_cmul (c d : G →₀ ℂ) (F : G → ℂ) : act (cmul c d) F = act c (act d F) := by
  funext y
  rw [act_apply, act_apply, cmul, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul]), act_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp [mul_assoc]

theorem act_single_one (F : G → ℂ) : act (Finsupp.single 1 1) F = F := by
  funext y; rw [act_apply, Finsupp.sum_single_index (by simp)]; simp

theorem act_mapDomain {H : Type} (f : H → G) (c : H →₀ ℂ) (F : G → ℂ) :
    act (Finsupp.mapDomain f c) F = c.sum fun h x => x • rTrans (f h) F := by
  rw [act, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]

theorem cmul_mem {S : Subgroup G} {c d : G →₀ ℂ} (hc : ∀ g, c g ≠ 0 → g ∈ S) (hd : ∀ g, d g ≠ 0 → g ∈ S) :
    ∀ g, cmul c d g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨a, ha, hga⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum (Finsupp.mem_support_iff.2 hg))
  obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hga)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hgb)]
  exact S.mul_mem (hc a (Finsupp.mem_support_iff.1 ha)) (hd b (Finsupp.mem_support_iff.1 hb))

theorem mapDomain_mem {H : Type} {S : Subgroup G} (f : H → G) (hf : ∀ h, f h ∈ S) (c : H →₀ ℂ) :
    ∀ g, Finsupp.mapDomain f c g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hg))
  exact hf h

def actL (c : G →₀ ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := act c
  map_add' F F' := by funext y; simp [act_apply, mul_add, Finsupp.sum_add]
  map_smul' r F := by funext y; simp [act_apply, Finsupp.mul_sum, mul_left_comm]

end Comb

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem isContAut_act {V : HSp D} (c : GA D V →₀ ℂ) {F : GA D V → ℂ} (hF : IsContAut V F) : IsContAut V (act c F) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [act_apply, act_apply]
    exact Finsupp.sum_congr fun h _ => by rw [mul_assoc, hF.1 γ hγ]
  · have : act c F = fun y => c.sum fun g x => x * F (y * g) := funext (act_apply c F)
    rw [this]
    exact continuous_finsetSum _ fun h _ => continuous_const.mul (hF.2.comp (continuous_id.mul continuous_const))

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem rep_eq (β : Frame p S n) (g : GL n k) (F : GA D S → ℂ) : β.rep g F = rTrans (β.gl g) F := rfl

theorem sum_rep_eq (β : Frame p S n) (c : GL n k →₀ ℂ) (F : GA D S → ℂ) :
    (c.sum fun g a => a • β.rep g F) = act (Finsupp.mapDomain β.gl c) F := by
  rw [act_mapDomain]; rfl

theorem ramAt_act (β : Frame p S n) (P : Pair k n) (c : GA D S →₀ ℂ)
    (hc : ∀ x, c x ≠ 0 → ∀ g, x * β.gl g = β.gl g * x) {φ₀ : GA D S → ℂ} (hφ : RamAt β P φ₀) :
    RamAt β P (act c φ₀) := by
  obtain ⟨φ, ⟨heq, hram, hcont⟩, rfl⟩ := hφ
  refine ⟨fun Q => actL c (φ Q), ⟨?_, ?_, fun Q => isContAut_act c (hcont Q)⟩, rfl⟩
  · intro g Q
    show act c (φ (g • Q)) = β.rep g (act c (φ Q))
    rw [heq g Q]
    funext y
    rw [rep_eq, rep_eq, act_apply]
    show _ = act c (φ Q) (y * β.gl g)
    rw [act_apply]
    refine Finsupp.sum_congr fun x hx => ?_
    simp only [rTrans]
    rw [mul_assoc, hc x (Finsupp.mem_support_iff.1 hx) g, mul_assoc]
  · let _ := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun Q => ?_
    have h0 := (mem_Mram φ).1 hram Q
    rw [← map_sum, h0, map_zero]

end Frames

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : ∀ x : GL (Fin V.rank) (AE D), Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) x =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor h) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) x) := by
    intro x; ext i j; simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem idAt_le_idOff {v w : Pl D} (h : v ≠ w) : idAt D (· = v) ≤ idOff D (· = w) := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = w := u.2
  exact ha.2 ⟨u.1, fun e => h (e.symm.trans hu)⟩

theorem grpAt_comm (V : HSp D) {v w : Pl D} (h : v ≠ w) {x y : GA D V} (hx : x ∈ grpAt V (· = w))
    (hy : y ∈ grpAt V (· = v)) : x * y = y * x :=
  (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).2 V |>.2.1 x hx y (congGrp_mono V (idAt_le_idOff h) hy)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {A S : HSp D}

theorem gl_mem {p₀ : SplitPt D k} (β : Frame p₀ A n) (g : GL n k) : β.gl g ∈ grpAt A (· = p₀.v) :=
  ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k p₀ A n β).1 _).2 ⟨g, rfl⟩

theorem sAll_cons (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (i : ι) (l : List ι) :
    a.sAll q χ ε (i :: l) = sOp (a.α i) (a.P i) q (χ i) (ε i) ∘ a.sAll q χ ε l := rfl

theorem place (a : PairDat p A S n) (hinj : Function.Injective fun i => (p i).v) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (i : ι) :
    (∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧ (∀ g, c' g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧
      (∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act c φ) ∧
      ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ sOp (a.α i) (a.P i) q (resChar χ hχ q) ε (act c' φ) = φ) ∧
    Set.MapsTo (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} {φ | a.Ram φ} ∧
    Set.InjOn (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} := by
  obtain ⟨hbij, -, c, c', hc, hc'⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q χ hχ _ rfl ε A (a.α i) (a.P i)
  have hC := mapDomain_mem _ (gl_mem (a.α i)) c
  have hC' := mapDomain_mem _ (gl_mem (a.α i)) c'
  have hT : ∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act (Finsupp.mapDomain (a.α i).gl c) φ :=
    fun φ => (hc φ).trans (sum_rep_eq _ _ _)
  have other : ∀ C₀ : GA D A →₀ ℂ, (∀ g, C₀ g ≠ 0 → g ∈ grpAt A (· = (p i).v)) → ∀ j, j ≠ i → ∀ φ,
      RamAt (a.α j) (a.P j) φ → RamAt (a.α j) (a.P j) (act C₀ φ) := fun C₀ hC₀ j hj φ hφ =>
    ramAt_act _ _ C₀ (fun x hx g => grpAt_comm A (fun e => hj (hinj e)) (hC₀ x hx) (gl_mem _ g)) hφ
  refine ⟨⟨_, _, hC, hC', hT, fun φ hφ => ?_⟩, fun φ hφ => ⟨?_, fun j => ?_⟩, hbij.injOn.mono fun φ hφ => hφ.2 i⟩
  · obtain ⟨h1, h2⟩ := hc' φ (hφ.2 i)
    rw [sum_rep_eq] at h1 h2
    refine ⟨⟨isContAut_act _ hφ.1, fun j => ?_⟩, h1⟩
    rcases eq_or_ne j i with rfl | hj
    · exact h2
    · exact other _ hC' j hj φ (hφ.2 j)
  · rw [hT]; exact isContAut_act _ hφ.1
  · rcases eq_or_ne j i with rfl | hj
    · exact hbij.mapsTo (hφ.2 j)
    · rw [hT]; exact other _ hC j hj φ (hφ.2 j)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl

open AllBij in

theorem allBijective_all : ∀ D : D7, AllBijective D := by
  intro D k _ _ _ _ ι p q χ hχ ε n _ _ A S a hinj I
  have hsub : ∀ i, grpAt A (· = (p i).v) ≤ grpAt A fun v => ∃ i, v = (p i).v :=
    fun i => congGrp_mono A (idAt_mono fun v hv => ⟨i, hv⟩)
  have key : ∀ I : List ι, Set.MapsTo (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      Set.InjOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ g, c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = act c φ) ∧
        ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (act c' φ) = φ := by
    intro I
    induction I with
    | nil =>
      have h1 : ∀ g, (Finsupp.single (1 : GA D A) (1 : ℂ)) g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v :=
        fun g h => by rw [(Finsupp.single_apply_ne_zero.1 h).1]; exact Subgroup.one_mem _
      refine ⟨fun φ h => h, fun φ _ ψ _ h => h, _, _, h1, h1, fun φ => (act_single_one φ).symm, fun φ h => ?_⟩
      rw [act_single_one]; exact ⟨h, rfl⟩
    | cons i l ih =>
      obtain ⟨⟨C, C', hC, hC', hT, hinv⟩, maps, inj⟩ := place a hinj q (χ i) (hχ i) (ε i) i
      obtain ⟨mapsl, injl, c, c', hc, hc', hl, hinvl⟩ := ih
      rw [sAll_cons]
      refine ⟨maps.comp mapsl, inj.comp injl mapsl, cmul C c, cmul c' C', cmul_mem (fun g h => hsub i (hC g h)) hc,
        cmul_mem hc' (fun g h => hsub i (hC' g h)), fun φ => ?_, fun φ hφ => ?_⟩
      · rw [act_cmul, ← hl, Function.comp_apply, hT]
      · rw [act_cmul]
        obtain ⟨h1, h2⟩ := hinv φ hφ
        obtain ⟨h3, h4⟩ := hinvl _ h1
        refine ⟨h3, ?_⟩
        rw [Function.comp_apply, h4, h2]
  obtain ⟨maps, inj, c, c', hc, hc', hT, hinv⟩ := key I
  exact ⟨⟨maps, inj, fun φ hφ => ⟨act c' φ, (hinv φ hφ).1, (hinv φ hφ).2⟩⟩, c, c',
    fun g h => h.elim (hc g) (hc' g), hT, hinv⟩

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealOcc

theorem pt_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T), ∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
      R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hF i t
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  have hL : GlobalTheory.RawLift.Laws R F := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  obtain ⟨-, v, w, -, hne⟩ := GlobalTheory.RawLift.vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ
  refine ⟨v, w, fun h => hne ?_⟩
  unfold GlobalTheory.RawLift.jointVec GlobalTheory.RawLift.thetaIP
  rw [h]
  simp

set_option maxHeartbeats 1000000 in

theorem real_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t y hy m hm
  obtain ⟨v, w, hJ⟩ := pt_ne D G Pl0 T A Ks R F hG.core hF i t
  have hw : w ≠ 0 := by
    rintro rfl
    refine hJ ?_
    rw [map_zero]
    unfold RealDat.ptP
    exact map_zero _
  have H2 := GlobalTheory.T.matrixCoeff_rightTranslate_definiteForm_scalar D G Pl0 T A Ks R F hG.core i t y m hm
  obtain ⟨z2, h2, h2ne⟩ := H2
  refine ⟨innerₛₗ ℂ w, R.ioP i (PiTensorProduct.tprod ℂ v) w, fun ν 𝓕 hν mR hmR => ?_⟩
  have H1 := GlobalTheory.T.weilCoefficient_pureTensor_eq_smul_inner D G Pl0 T A Ks R F hG.core hF i t v ν 𝓕 hν
  obtain ⟨z1, h1, h1ne⟩ := H1
  have e1 : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ :=
    fun b => h1 w b b.2
  have e : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b *
        GlobalTheory.Core.Rk.IP.rcoef m (fun g => innerₛₗ ℂ w (R.extV i t y g)) (fun g => innerₛₗ ℂ w (R.extV i t y g)) b =
      (z1 * z2) * ((‖⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun b => by
    calc _ = (z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ) * (z2 * ⟪(R.cV i).ρ (b : GA D (Vc D i)) w, w⟫_ℂ) :=
          congrArg₂ (· * ·) (e1 b) (h2 w b b.2)
      _ = _ := by
        rw [← inner_conj_symm ((R.cV i).ρ (b : GA D (Vc D i)) w) w, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, integral_complex_ofReal]
  exact mul_ne_zero (mul_ne_zero (h1ne w hJ) (h2ne hy)) (Complex.ofReal_ne_zero.2
    (GlobalTheory.T.integral_normSq_matrix_coefficient_ne_zero_definite D (Vc D i) (D.sp.V_sig _) (hG.core.models.vpos i) (R.cV i) (hG.core.models.cV i) w hw mR hmR))

end GlobalTheory.Core.Rk.RealOcc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwistStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_level_integral_twist : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  first | exact @GlobalTheory.CongFlag.resS_eq_of_flag | exact GlobalTheory.CongFlag.resS_eq_of_flag | (intros; apply GlobalTheory.CongFlag.resS_eq_of_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLineIdealEqInverseDifferentPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow | exact GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow | (intros; apply GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductorStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_complement_frame_diag_mod_conductor : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  first | exact @GlobalTheory.ScalW.scalar_diag_mod_g | exact GlobalTheory.ScalW.scalar_diag_mod_g | (intros; apply GlobalTheory.ScalW.scalar_diag_mod_g <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  first | exact @GlobalTheory.MovedDat.locF_eq_iterPhi | exact GlobalTheory.MovedDat.locF_eq_iterPhi | (intros; apply GlobalTheory.MovedDat.locF_eq_iterPhi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S), IsSelfDualC S L → (∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) → IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | exact GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | exact GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | (intros; apply GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one <;> assumption)
end

