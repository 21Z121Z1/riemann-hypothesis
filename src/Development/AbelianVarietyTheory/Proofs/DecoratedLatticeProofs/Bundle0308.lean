import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.UnitPlaces

variable {D : D7}

theorem pairA_sum {κ : Type} (s : Finset κ) (f : κ → Af D.host.F) :
    pairA D.host.F 0 (∑ i ∈ s, f i) = ∑ i ∈ s, pairA D.host.F 0 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.FinPlLoc.pairA_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.FinPlLoc.pairA_add, ih]

theorem latMul_mono (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latMul S 𝔞 L P ≤ latMul S 𝔞 L P' := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact AddSubgroup.subset_closure ⟨α, hαi, fun v hv => hα v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem latMul_le_of_parts (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (M : AddSubgroup (Fin S.rank → AE D))
    {P : Pl D → Prop} (s : Finset (Pl D)) (hs : ∀ w, P w → w ∈ s) (h : ∀ w ∈ s, latMul S 𝔞 L (· = w) ≤ M) :
    latMul S 𝔞 L P ≤ M := by
  classical
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  have hdec : α = ∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α := by
    refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α)
    rw [map_sum]
    simp only [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u ∈ s
    · simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos hu]
    · have h0 : evalV D.host.F u α = 0 := hα u fun h' => hu (hs u h')
      simp [h0]
  have hsum : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
      ∑ w ∈ s, fun i => pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = w) * α) ⊗ₜ[D.host.F] (a * x i) := by
    funext i
    rw [Finset.sum_apply, ← TensorProduct.sum_tmul, ← pairA_sum, ← hdec]
  show _ ∈ M
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun w hw => h w hw (AddSubgroup.subset_closure
    ⟨GlobalTheory.FinPlLoc.ePl D (· = w) * α, fun u => ?_, fun u hu => ?_, a, ha, x, hx, rfl⟩)
  · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ u) (hαi u)
  · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hu, zero_mul]

theorem latA_eq_latV : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  intro D k _ _ _ _ ι p I P hP S L
  classical
  let s : Finset (Pl D) := (I.map fun i => (p i).v).toFinset
  have hs : ∀ w, P w → w ∈ s := by
    intro w hw
    obtain ⟨i, rfl⟩ := (hP.mem w).1 hw
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨i, hP.all i, rfl⟩)
  have hsi : ∀ w ∈ s, ∃ i, w = (p i).v := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
    exact ⟨i, rfl⟩
  have hsP : ∀ w ∈ s, P w := fun w hw => (hP.mem w).2 (hsi w hw)
  have hloc : ∀ w ∈ s, latA S L (· = w) = latV S L (· = w) := by
    intro w hw
    obtain ⟨i, rfl⟩ := hsi w hw
    exact (hP.unit i).2 S L
  apply le_antisymm
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).le.trans (latMul_mono S {1} L fun u (hu : u = w) => hu ▸ hsP w hw)
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).ge.trans (latMul_mono S {a | a ∈ D.host.AA} L fun u (hu : u = w) => hu ▸ hsP w hw)

end GlobalTheory.FinPl.UnitPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesSelfDualOfSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SelfDualCompl

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

def hA (S : HSp D) (y s : Fin S.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j

theorem intAt_zero (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem hA_zero_left (S : HSp D) (s : Fin S.rank → AE D) : hA S 0 s = 0 := by
  simp [hA]

theorem hA_add_left (S : HSp D) (y y' s : Fin S.rank → AE D) : hA S (y + y') s = hA S y s + hA S y' s := by
  simp [hA, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (y s : Fin S.rank → AE D) : hA S (-y) s = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (y : Fin S.rank → AE D) : hA S y 0 = 0 := by
  simp [hA]

theorem hA_add_right (S : HSp D) (y s s' : Fin S.rank → AE D) : hA S y (s + s') = hA S y s + hA S y s' := by
  simp [hA, add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (y s : Fin S.rank → AE D) : hA S y (-s) = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    hA S (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x j)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (∑ i, ∑ j, star (x' i) * HSpace.gram S i j * x j) := by
  simp only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum,
    pairA_mul]

theorem hA_mem {S : HSp D} {LS : Lat S} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {y s : Fin S.rank → AE D}
    (hy : y ∈ latV S LS P) (hs : s ∈ latV S LS P) : hA S y s ∈ intAt D P := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβi, hβ, a, ha, x', hx', rfl⟩ := hs
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hA_gen]
      obtain ⟨c, hc⟩ := (hS.2 x).1 hx x' hx'
      rw [← hc]
      refine ⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [finPart_pair]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩
    | zero => rw [hA_zero_left]; exact intAt_zero P
    | add y y' _ _ h h' => rw [hA_add_left]; exact intAt_add h h'
    | neg y _ h => rw [hA_neg_left]; exact intAt_neg h
  | zero => rw [hA_zero_right]; exact intAt_zero P
  | add s s' _ _ h h' => rw [hA_add_right]; exact intAt_add h h'
  | neg s _ h => rw [hA_neg_right]; exact intAt_neg h

theorem wachExpansion_smul_compatible {S : HSp D} {LS : Lat S} (P : Pl D → Prop) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (idem D P * finIn D z) • (fun l => incA D (s l)) ∈ latV S LS P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha,
      fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul,
      mul_one, one_mul]
    congr 1
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add, mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

theorem smul_mem {S : HSp D} {LS : Lat S} {P : Pl D → Prop} {c : AE D} (hc : c ∈ intAt D P) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) : c • (fun l => incA D (s l)) ∈ latV S LS P := by
  have h1 : idem D P * c = c := (mem_idAt_iff P c).1 hc.1
  have h2 : c = finIn D (finPart D c) := eq_finIn (infPart_of_idAt hc.1)
  have := wachExpansion_smul_compatible P hs hc.2
  rwa [← h2, h1] at this

theorem cA_test (P : Pl D → Prop) (e : D.host.E) :
    cA D (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * e)) = idem D P * incA D (star e) := by
  rw [cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]

theorem selfDual_latV : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop)
    (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) →
    (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  intro D S LS hS P y hy
  refine ⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  let t : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)
  have ht : ∀ i, t i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩
  have hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a)) := by
    funext a
    have hya : y a = idem D P * y a := ((mem_idAt_iff P (y a)).1 (hy a)).symm
    have hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0 := by
      intro j
      split_ifs <;> simp
    calc y a = ∑ j, idem D P * y j * incA D (if a = j then 1 else 0) := by
          rw [Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
          exact hya
      _ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by
          simp only [hdual]
      _ = _ := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hyeq]
  exact sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)

end GlobalTheory.FinPl.SelfDualCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.LeviSplitChar

theorem circle_eq_one_of_pos {u : Circle} {t : ℝ} (ht : 0 < t) (h : (u : ℂ) = t) : u = 1 := by
  have h1 : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
  apply Circle.ext
  rw [h, h1, Circle.coe_one]
  simp

variable {D : D7}

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  simp [Formalism.L2.Theta.SuppAt, Formalism.L2.Theta.mt]

theorem isDetAt_one (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  simp [Formalism.L2.Theta.IsDetAt, Formalism.L2.Theta.mt]

end GlobalTheory.LeviSplitChar

namespace GlobalTheory.LeviSplitChar

variable {D : D7}

theorem exists_form (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T)
    (hω : IsWeilDatumO ψ S T χS χT om) (hω₀ : IsWeilDatumO ψ S₀ T χS χT om₀)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle)
    (H : ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 =
      ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0))
    (e : AE D) (he : IsSplitIdem D e) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧
      ∀ a g, SuppAt e S₀ g → ∀ x₀, IsDetAt e S₀ g x₀ → ∃ R : ℝ, 0 < R ∧ ∀ f, IsThetaFunO ψ S T f →
        ℓ (om (d.levi a * d.emb0 g, 1) f) = (R : ℂ) * ((α a : ℂ) * (ξ g : ℂ) * (splitFacO χS χT x₀ 1 : ℂ)) * ℓ f := by
  obtain ⟨ℓ₀, hinv₀, f₀, hf₀, hne₀⟩ := GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form D ψ hω.std S₀ T e he
  obtain ⟨ℓ, hinv, hne, hcmp⟩ := GlobalTheory.T.exists_splitPlace_invariantForm_of_wittCore D ψ hω.std S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hinv₀ ⟨f₀, hf₀, hne₀⟩
  refine ⟨ℓ, hinv, hne, fun a g hg x₀ hx₀ => ?_⟩
  obtain ⟨r₀, hr₀, hsp₀⟩ := hω₀.om_split e he g 1 hg (suppAt_one e T) x₀ 1 hx₀ (isDetAt_one e T)
  obtain ⟨r, hr, hc⟩ := hcmp 1 a
  have hmv := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hω.std).1 S S₀ T ρ d μ 𝓕 hμ
  have hbr := (GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1
  have hm := GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod_pos T.rank a
  refine ⟨r * r₀ * GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a, by positivity, fun f hf => ?_⟩
  have key := hc f (om (d.levi a * d.emb0 g, 1) f)
    ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ) * (r₀ : ℂ) * (splitFacO χS χT x₀ 1 : ℂ))
    hf (hω.om_pres _ f hf) (fun x _ => ?_)
  · rw [key]; push_cast; ring
  · have hmove := (GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x).2.1 a g
    rw [hmove, H a g _ (GlobalTheory.TwistFactorCompare.isTheta_heisO hω.std hf _), ← hbr μ 𝓕 f (x ⬝ a.1), map_smul,
      smul_eq_mul, hsp₀ ℓ₀ hinv₀ _ (hmv f hf _)]
    simp only [Units.val_one, Matrix.one_mul]
    ring

end GlobalTheory.LeviSplitChar

namespace GlobalTheory.LeviSplitChar

theorem levi_chars_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), (∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0)) → ∀ e, IsSplitIdem D e → (∀ g, SuppAt e S₀ g → ξ g = 1) ∧ ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hω hω₀ μ 𝓕 hμ α ξ H e he
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩, hkey⟩ := exists_form ψ S S₀ T ρ d χS χT om om₀ hω hω₀ μ 𝓕 hμ α ξ H e he
  have hsd := GlobalTheory.T.splitPlace_determinants_wittLeviFactor D S S₀ ρ d e he
  constructor
  · intro g hg
    obtain ⟨hS, x, hx₀, hx⟩ := hsd.1 g hg
    obtain ⟨R, hR, hk⟩ := hkey 1 g hg x hx₀
    obtain ⟨r', hr', hsp⟩ := hω.om_split e he (d.emb0 g) 1 hS (suppAt_one e T) x 1 hx (isDetAt_one e T)
    have h1 := hk f hf
    have h2 := hsp ℓ hinv f hf
    rw [map_one, one_mul] at h1
    rw [h1, map_one, Circle.coe_one] at h2
    have hs : (splitFacO χS χT x 1 : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : (R : ℂ) * (ξ g : ℂ) = r' := by
      have := mul_right_cancel₀ hℓf (by rw [← h2]; ring : ((R : ℂ) * (ξ g : ℂ)) * (splitFacO χS χT x 1 : ℂ) * ℓ f = (r' : ℂ) * (splitFacO χS χT x 1 : ℂ) * ℓ f)
      exact mul_right_cancel₀ hs this
    apply circle_eq_one_of_pos (div_pos hr' hR)
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    rw [← h3]
    field_simp
  · intro a ha
    obtain ⟨hS, x, hx, hχ⟩ := hsd.2 χT T.rank hω.hecT hω.resT a ha
    obtain ⟨R, hR, hk⟩ := hkey a 1 (suppAt_one e S₀) 1 (isDetAt_one e S₀)
    obtain ⟨r', hr', hsp⟩ := hω.om_split e he (d.levi a) 1 hS (suppAt_one e T) x 1 hx (isDetAt_one e T)
    have h1 := hk f hf
    have h2 := hsp ℓ hinv f hf
    rw [map_one, mul_one] at h1
    rw [h1] at h2
    simp only [splitFacO, map_one, inv_one, mul_one, Circle.coe_one, hχ, Circle.coe_mul, Circle.coe_inv] at h2
    have hd : ((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : (R : ℂ) * ((α a : ℂ) * (χT (Matrix.GeneralLinearGroup.det a) : ℂ)) = r' := by
      have := mul_right_cancel₀ hℓf h2
      rw [← mul_assoc, this]
      field_simp
    have hu : α a * χT (Matrix.GeneralLinearGroup.det a) = 1 := by
      apply circle_eq_one_of_pos (div_pos hr' hR)
      have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      push_cast
      rw [← h3]
      field_simp
    exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory.LeviSplitChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarFiniteOnCompacts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR
namespace RDecomp

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem blocks_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, r.val.toBlocks₁₁ = x.val ∧ (r⁻¹).val.toBlocks₁₁ = (x⁻¹).val := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  refine ⟨x, GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu, ?_⟩
  have e : (embX c x * u)⁻¹ = embX c x⁻¹ * (embX c x * u⁻¹ * (embX c x)⁻¹) := by
    rw [map_inv]; group
  rw [e]
  exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x⁻¹ (GlobalTheory.RootEx.Radical.conj_mem x (inv_mem hu))

def gpart (r : R k n c p) : GL n k :=
  ⟨(r : GL (n ⊕ Fin c) k).val.toBlocks₁₁, ((r : GL (n ⊕ Fin c) k)⁻¹).val.toBlocks₁₁,
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.mul_inv],
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.inv_mul]⟩

theorem gpart_prodR (q : GL n k × N k n c p) : gpart (prodR p q) = q.1 :=
  Units.ext (GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul q.1 q.2.2)

theorem mem_N_of_mem_R (r : R k n c p) : (embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k) ∈ N k n c p := by
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R r.2
  have : gpart r = x := Units.ext (by
    change (r : GL (n ⊕ Fin c) k).val.toBlocks₁₁ = _
    rw [e]; exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu)
  rw [this, e, inv_mul_cancel_left]
  exact hu

def upart (r : R k n c p) : N k n c p := ⟨(embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k), mem_N_of_mem_R r⟩

end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_gpart (p : ℕ) : Continuous (gpart (k := k) (n := n) (c := c) (p := p)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp continuous_subtype_val
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp (continuous_subtype_val.inv)

def prodRHomeo (p : ℕ) : GL n k × N k n c p ≃ₜ R k n c p where
  toFun := prodR p
  invFun r := (gpart r, upart r)
  left_inv q := by
    have h := gpart_prodR (c := c) q
    refine Prod.ext h (Subtype.ext ?_)
    change (embX c (gpart (prodR p q)))⁻¹ * (embX c q.1 * (q.2 : GL (n ⊕ Fin c) k)) = _
    rw [h, inv_mul_cancel_left]
  right_inv r := Subtype.ext (by
    change embX c (gpart r) * ((embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k)) = _
    rw [mul_inv_cancel_left])
  continuous_toFun := Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun := (continuous_gpart p).prodMk (Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_gpart p)).inv.mul continuous_subtype_val) _)

end

end RDecomp
open RDecomp

theorem finite_r : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts ((m.prod (volN ν n c p)).map (prodR p)) := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν hν m hm
  haveI := hν
  haveI := hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : (volN ν n c p).IsHaarMeasure := GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν p
  haveI : LocallyCompactSpace (N k n c p) := (GlobalTheory.RootEx.VolN.isClosed_N p).locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  have e : ⇑(prodRHomeo (k := k) (n := n) (c := c) p) = prodR p := rfl
  rw [← e]
  exact Measure.IsFiniteMeasureOnCompacts.map _ (prodRHomeo p)

end GlobalTheory.HaarR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanLogCovolumeConjugateLatticesEq
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.MeanLogArea

theorem mean_log_area : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hn : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  have hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) =
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) +
        (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Real.log_div (hpos ρ).ne' Real.pi_pos.ne']
    ring
  rw [hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]
  unfold ClassMeanPeriods.classMeanValue
  rw [hmean]
  ring

end GlobalTheory.MeanLogArea
end
end

