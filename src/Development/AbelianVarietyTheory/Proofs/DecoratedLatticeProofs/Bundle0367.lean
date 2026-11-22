import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoreIffCollapsesWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitOnto

variable {D : D7}

theorem eq_zero_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

theorem moves_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} : Moves S 1 L L P := by
  intro y _
  rw [PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem moves_list_prod {S : HSp D} {L : Lat S} {P : Pl D → Prop} :
    ∀ l : List (GA D S), (∀ a ∈ l, Moves S a L L P) → Moves S l.prod L L P
  | [], _ => by rw [List.prod_nil]; exact moves_one
  | a :: l, h => by
    rw [List.prod_cons]
    exact PlacesAdeles.moves_mul (h a List.mem_cons_self) (moves_list_prod l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem prod_ofFn_single {M : Type*} [Monoid M] :
    ∀ {r : ℕ} (f : Fin r → M) (i : Fin r), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | r + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hi : i = 0
    · subst hi
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero j)
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact prod_ofFn_single (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

def locHom (S : HSp D) {k : Type} [Ring k] (f : AE D →+* k) : GA D S →* Matrix (Fin S.rank) (Fin S.rank) k where
  toFun a := (mt S a).map f
  map_one' := by rw [PlacesAdeles.mt_one]; exact Matrix.map_one f f.map_zero f.map_one
  map_mul' a b := by rw [PlacesAdeles.mt_mul]; exact Matrix.map_mul

section Place

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_off (q : SplitPt D k) {a : AE D} (ha : a ∈ idOff D (· = q.v)) : q.pr a = 0 := by
  have h1 : q.e * a = 0 := eq_zero_at_off (· = q.v)
    (Ideal.mul_mem_right a _ (FrameLat.e_mem_idAt (p := q))) (Ideal.mul_mem_left _ q.e ha)
  have h2 : q.pr q.e = 1 := by rw [← FrameLat.sec_one (p := q), q.pr_sec]
  calc q.pr a = q.pr q.e * q.pr a := by rw [h2, one_mul]
    _ = 0 := by rw [← map_mul, h1, map_zero]

theorem map_off (q : SplitPt D k) {S : HSp D} {b : GA D S} (hb : b ∈ grpOff S (· = q.v)) :
    (mt S b).map q.pr = 1 := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  ext i j
  have h := pr_off q (hb i j)
  rw [map_sub, sub_eq_zero] at h
  rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem one_place (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) (q : SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) (hI : IntIn q S F N) (x : GL Y k) (hx : x ∈ GlobalTheory.SplitWeil.KO k Y) :
    ∃ g, InK S N (· = q.v) g ∧ (mt S g).map q.pr = F.β * x.val * F.γ := by
  classical
  have H := (GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.Place.ofSplitPt q)).1 S Y F
  choose glf hglf using fun gk => (H.1 gk).exists
  let gl : GL Y k →* GA D S := MonoidHom.mk' glf fun a b =>
    (H.1 (a * b)).unique (hglf (a * b)) (H.2.2 _ _ _ _ (hglf a) (hglf b))
  let β : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun g => (hglf g).1, fun g => (hglf g).2⟩
  obtain ⟨Λ, -, hΛ, hK⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y β N hN
  have hmem : ∀ y : Y → k, y ∈ Λ ↔ ∀ j, y j ∈ 𝒪[k] := fun y => (hΛ y).trans (hI y).symm
  obtain ⟨x₀, rfl⟩ := hx
  have hint : ∀ (z : GL Y 𝒪[k]) (y : Y → k), (∀ j, y j ∈ 𝒪[k]) →
      ∀ j, (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z • y) j ∈ 𝒪[k] := by
    intro z y hy j
    change ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z).val *ᵥ y) j ∈ 𝒪[k]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun l _ => mul_mem (z.val j l).2 (hy l)
  have hstab : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀ • Λ = Λ := by
    ext y
    rw [GlobalTheory.LatPair.mem_smul_iff, hmem, hmem]
    constructor
    · intro h
      have := hint x₀ _ h
      rwa [smul_inv_smul] at this
    · intro h
      rw [← map_inv]
      exact hint x₀⁻¹ y h
  exact ⟨β.gl _, (hK _).2 hstab, (hglf _).2⟩

end Place

theorem exists_of_local : ∀ {D : D7} (S : HSp D) (N : Lat S), IsSelfDualC S N → ∀ {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i)), Function.Injective (fun i => (q i).v) → (∀ i, IntIn (q i) S (F i) N) → ∀ x : (i : Fin r) → GL (Y i) (k i), (∀ i, x i ∈ GlobalTheory.SplitWeil.KO (k i) (Y i)) → ∃ g, InK S N (fun p => ∃ i, (q i).v = p) g ∧ ∀ i, (mt S g).map (q i).pr = (F i).β * (x i).val * (F i).γ := by
  intro D S N hN r k _ _ _ _ q Y _ _ F hinj hI x hx
  classical
  choose g hgK hgm using fun i => one_place S N hN (q i) (F i) (hI i) (x i) (hx i)
  have hgrp : ∀ i, g i ∈ grpAt S (· = (q i).v) := fun i => (hgK i).1
  have hoff : ∀ i j, j ≠ i → g j ∈ grpOff S (· = (q i).v) := fun i j hji =>
    PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_le_idOff (fun e => hji (hinj e).symm)) (hgrp j)
  refine ⟨(List.ofFn g).prod, ⟨?_, ?_⟩, ?_⟩
  · refine _root_.list_prod_mem fun a ha => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_single_le ⟨j, rfl⟩) (hgrp j)
  · have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun p => ∃ i, (q i).v = p)).2 S).2.2.2 N
    have hloc : ∀ i, Moves S (List.ofFn g).prod N N (· = (q i).v) := fun i =>
      moves_list_prod _ fun a ha => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
        by_cases hji : j = i
        · subst hji; exact (hgK j).2
        · exact moves_off (hoff i j hji)
    intro y hy
    rw [hlat y hN.1, hlat _ hN.1]
    have hy' := PlacesAdeles.supp_mulVec S _ (List.ofFn g).prod hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ ⟨i, rfl⟩ e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      have := h2 _ ⟨i, rfl⟩ e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · intro i
    change locHom S (q i).pr (List.ofFn g).prod = _
    rw [map_list_prod, List.map_ofFn, prod_ofFn_single _ i]
    · exact hgm i
    · intro j hji
      exact map_off (q i) (hoff i j hji)

end GlobalTheory.SplitOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitWeilChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (q : SplitPt D k) (hU : q.UnitAA) : q.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := GlobalTheory.SplitCharCond.exists_idem q
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = q.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := GlobalTheory.SplitCharCond.pr_int q (hU.1 _ hm).2.2
  rwa [map_mul, GlobalTheory.SplitCharCond.pr_pair_tmul q h, map_one, map_one, mul_one] at this

theorem valuation_pr_incA_xi0_eq_one_of_unitAA (q : SplitPt D k) (hU : q.UnitAA) : valuation k (q.pr (incA D D.host.xi0)) = 1 := by
  have h1 := (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitCharCond.xi_zero_projection_integral q hU)
  have h2 := (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hm : q.pr (incA D D.host.xi0) * q.pr (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  have h3 := congrArg (valuation k) hm
  rw [map_mul, map_one] at h3
  by_contra hne
  have hlt : valuation k (q.pr (incA D D.host.xi0)) < 1 := lt_of_le_of_ne h1 hne
  have : valuation k (q.pr (incA D D.host.xi0)) * valuation k (q.pr (incA D D.host.xi0⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitWeilChar

namespace GlobalTheory.SplitWeilChar

theorem weil_char_conductor_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  intro D k _ _ _ _ q ψ hψ hU
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  set u : k := q.pr (incA D D.host.xi0) with hu
  have hv : valuation k u = 1 := valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  let χ : AddChar k Circle := ψk.mulShift u⁻¹
  have hχ : q.IsChar ψ χ := by
    intro a
    have e1 : (χ a : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec (u⁻¹ * a)) := hk (u⁻¹ * a)
    have e2 := GlobalTheory.SplitCharCond.sec_mul_pr q (u⁻¹ * a) (incA D D.host.xi0)
    rw [← hu, show u⁻¹ * a * u = a by field_simp] at e2
    rw [e1, ← e2]
  have hc1 : HasConductor χ 1 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ χ hψ hχ hU
  have hcu : HasConductor χ (Units.mk0 u hu0) := by
    intro x
    rw [Units.val_mk0, hv]
    have := hc1 x
    rwa [Units.val_one, map_one] at this
  have he : ψk = χ.mulShift ((Units.mk0 u hu0 : kˣ) : k) := by
    ext x
    simp only [χ, AddChar.mulShift_apply, Units.val_mk0]
    rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  refine ⟨ψk, hk, ?_⟩
  rw [he]
  exact GlobalTheory.CollapseCompare.hasConductor_mulShift hcu

end GlobalTheory.SplitWeilChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SymChainAt
open GlobalTheory.FinPl (SplitPt idAt intAt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem pr_e_mul (x : AE D) : q.pr (q.e * x) = q.pr x := by rw [map_mul, pr_e, one_mul]

theorem place_facts {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pr_e_mul, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pr_e_mul]

def prO : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prO_le {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) : valuation k (prO q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (((place_facts q h).1 _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

theorem prO_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prO q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prO q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prO q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prO_eq_one {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {z : 𝓞 D.host.E} (hz : z ∉ PP.asIdeal) :
    valuation k (prO q z) = 1 := le_antisymm (prO_le q h z) (not_lt.1 (mt (prO_lt q h z).2 hz))

theorem sec_mul (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idl_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul q x y
  rw [h, sec_one] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idl (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idl_mul q _ _ x.mul_inv, idl_mul q _ _ x.inv_mul⟩

theorem continuous_idl : Continuous (idl q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem unram_idl {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (x : kˣ) (hx : valuation k (x : k) = 1) :
    χ (idl q x) = 1 := by
  have one : finPart D 1 ∈ intAE D := by
    rw [map_one]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simp, 1, rfl⟩
  have key : ∀ y : k, valuation k y ≤ 1 → finPart D (q.sec y + (1 - q.e)) ∈ intAE D := fun y hy => by
    rw [RingHom.map_add, RingHom.map_sub, ← sec_one]
    exact add_mem ((q.int_iff y).1 hy) (sub_mem one ((q.int_iff 1).1 (one_mem _)))
  refine hχ _ ?_ (key _ hx.le) (key _ (by simp [hx]))
  have h1 : infPart D (q.sec x) = 0 := (GlobalTheory.FrameGlob.sec_mem_idAt q x).1
  have h2 : infPart D q.e = 0 := (GlobalTheory.FrameGlob.e_mem_idAt q).1
  change infPart D (q.sec x + (1 - q.e)) = 1
  rw [RingHom.map_add, RingHom.map_sub, h1, h2, RingHom.map_one, zero_add, sub_zero]

theorem res_idl {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hχ : Formalism.IndefR.Links.ChrEq χ H) (hr : Formalism.IndefR.Links.IsRes H PP c) (x : kˣ)
    (hx : valuation k ((x : k) - 1) < 1) : χ (idl q x) = 1 := by
  obtain ⟨hi, hd⟩ := place_facts q h
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 → χ (idl q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    obtain ⟨r, s, hs, e⟩ := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have e' : prO q s * y = prO q r := by
      rw [hy]
      exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
    have hrs : r - s ∈ PP.asIdeal := by
      rw [prO_lt q h, map_sub, ← e', ← mul_sub_one, map_mul, prO_eq_one q h hs, one_mul]
      exact hy1
    have hs0 : (s : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact y.ne_zero (hy.trans (q.pr.comp (incA D)).map_zero)
    haveI := PP.isMaximal
    letI := Ideal.Quotient.field PP.asIdeal
    have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
    have h2 := hr r (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu) e (Ideal.Quotient.eq.2 hrs).symm
    rw [map_mul, ← h1, left_eq_mul] at h2
    have h3 := hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idl q y) (by
        change q.sec y + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hy]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)
    rw [h2] at h3
    exact Circle.coe_injective h3
  by_contra hne
  have hc : Continuous fun y => χ (idl q y) := hχ.1.1.comp (continuous_idl q)
  have h1 : {y : kˣ | χ (idl q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

theorem tame_comp {c : GlobalTheory.ChainOnto.Com D} (hc : c.Is) {PP : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ c.Pg) (h : IsIdemAt q.e PP)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ} (hμ : (ofSplit q).IsComp (c.chS j)⁻¹ μ) : IsTame μ := by
  intro x hx
  have hv : valuation k (x : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨H, hH, hr⟩ := hc.res ⟨i, h2⟩
  have e1 := res_idl q h hH (hr PP hP) x hx
  have e2 := unram_idl q hc.chars.2.1 x hv
  have e3 : c.chS (i + 1) (idl q x) = 1 := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs
    · change c.μ (i + 1) (idl q x) * (c.η (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

end Place

theorem exists_symData_at : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), d.c.Is → PP ∈ d.c.Pg →
    Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar d.c.ψ ψk → HasConductor ψk 1 →
    ∀ s ρ : ℕ, s = 2 * ρ → ∃ S : SymData k s D.R.k, S.ψ = ψk ∧
      ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j) := by
  intro D u d k _ _ _ _ q PP hc hP h ψk _ hψ s ρ hs
  subst hs
  classical
  let μ : ℕ → kˣ →* ℂˣ := fun j =>
    if 1 ≤ j ∧ j ≤ D.R.m then Classical.choose (Witness.exists_isComp (ofSplit q) (d.c.chS j)⁻¹) else 1
  have hμ : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (μ j) := fun j h1 h2 => by
    simp only [μ, if_pos (And.intro h1 h2)]
    exact Classical.choose_spec (Witness.exists_isComp (ofSplit q) (d.c.chS j)⁻¹)
  have htame : ∀ j, IsTame (μ j) := fun j => by
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · exact tame_comp q hc hP h hj.1 hj.2 (hμ j hj.1 hj.2)
    · simp only [μ, if_neg hj]
      intro x _
      rfl
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using ht.symm)
  have hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif (Units.mk0 t ht0) := fun x => by
    rw [Units.val_mk0, ht]
    exact le_uniformizer_iff.symm
  obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel k ψk hψ _ hϖ ρ D.R.k (2 * ρ + 1)
  exact ⟨SymData.mk ψk (Units.mk0 t ht0) ρ P μ htame hψ hϖ rfl hP', rfl, hμ⟩

end GlobalTheory.LocMod.SymChainAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficient_realPlace_two_vacua : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (τ : D.what₂.Tau) (f F F' : WO V W → ℂ), (∀ x ∈ [f, F, F'], IsThetaFunO ψ V W x ∧ IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ P Q : LPol W.rank V.rank, let pt := GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ); GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt F P)) (pt F' Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt f P)) (pt f Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X F F' := by
  first | exact @GlobalTheory.VacCoefAtPlace.coef_at_place | exact GlobalTheory.VacCoefAtPlace.coef_at_place | (intros; apply GlobalTheory.VacCoefAtPlace.coef_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialJetValueEqJetLinearFormRescaledStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled : ∀ (D : D7) (S T : HSp D) (s : ℂ) (cD : D.what₂.Tau → ℂ), (∀ τ, cD τ ≠ 0) → ∀ (G : VCx D.what₂.Tau S.rank T.rank → ℂ) (P : FP D.what₂.Tau S.rank T.rank), jetP S T rfl rfl s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) P) := by
  first | exact @GlobalTheory.KJInf.jetP_eq_jetL | exact GlobalTheory.KJInf.jetP_eq_jetL | (intros; apply GlobalTheory.KJInf.jetP_eq_jetL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.Fold.fold_quot | exact GlobalTheory.Core.Mi.Fold.fold_quot | (intros; apply GlobalTheory.Core.Mi.Fold.fold_quot <;> assumption)
end

