import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_intAt (q : GlobalTheory.FinPl.SplitPt D k) : q.e ∈ intAt D (· = q.v) := by
  refine ⟨GlobalTheory.FrameGlob.e_mem_idAt q, ?_⟩
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  have h := (q.int_iff 1).1 (one_mem _)
  rwa [h1] at h

theorem smul_mem_latV {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : Submodule.IsLattice D.host.E L) {v : GlobalTheory.FinPl.Pl D}
    {z : Fin V.rank → AE D} (hz : z ∈ latV V L (· = v)) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    a • z ∈ latV V L (· = v) :=
  ((((GlobalTheory.FinPl.localComponents D (· = v)).2 V).2.2.2 L z hL).1 hz).2 v rfl a ha

theorem sec_pr_mul (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (c : k) : q.sec (q.pr a * c) = a * q.sec c := by
  calc q.sec (q.pr a * c) = q.sec (q.pr (a * q.sec c)) := by rw [RingHom.map_mul q.pr, q.pr_sec]
    _ = q.e * (a * q.sec c) := q.sec_pr _
    _ = a * q.sec c := by rw [mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul]

theorem sec_int_iff (q : GlobalTheory.FinPl.SplitPt D k) (c : k) :
    toEAf D (q.sec c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ c ∈ 𝒪[k] := by
  have h := q.pr_mem_iff (q.sec c)
  rw [q.pr_sec, ← map_mul, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem sec_mem_iff (V : HSp D) (t : GA D V) (Λ L : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D))
    (q : GlobalTheory.FinPl.SplitPt D k) (M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hm : GlobalTheory.FinPl.Moves V t Λ L (· = q.v)) (hM : MovedTo (ofSplit q) V t β M)
    (x : Fin V.rank → k) :
    (fun i => q.sec ((M *ᵥ x) i)) ∈ latV V L (· = q.v) ↔ ∀ i, x i ∈ 𝒪[k] := by
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin V.rank) (Fin V.rank) (AE D), b.map (toEAf D) = β.val := by
    choose f hf using fun s : Lev.EAf D => GlobalTheory.ResLoc.toEAf_surj (D := D) s
    exact ⟨β.val.map f, by ext i j; simp [hf]⟩
  set s : Fin V.rank → AE D := fun i => q.sec (x i) with hsdef
  have hs : ∀ i, s i ∈ idAt D (· = q.v) := fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _
  have hy : ∀ i, (b *ᵥ s) i ∈ idAt D (· = q.v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hs j)
  have hkey : (fun i => q.sec ((M *ᵥ x) i)) = Formalism.L2.Theta.mt V t *ᵥ (b *ᵥ s) := by
    rw [Matrix.mulVec_mulVec, ← hM b hb]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact sec_pr_mul q _ _
  rw [hkey, ← hm _ hy]
  have hbridge : b *ᵥ s ∈ latV V Λ (· = q.v) ↔
      (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ⟨GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _, GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy⟩
  rw [hbridge, hβ]
  have h2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) = β.val *ᵥ fun i => toEAf D (s i) := by
    funext i
    change toEAf D ((b *ᵥ s) i) = _
    rw [← hb]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum (toEAf D)]
    simp only [RingHom.map_mul]
  rw [h2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact forall_congr' fun i => sec_int_iff q (x i)

end GlobalTheory.SplitFrameLat

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

theorem latV_eq : ∀ {D : D7} (V : HSp D) (t : GA D V) (Λ L N : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (σ : Fin V.rank ≃ Y), t ∈ GfC V → IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V t Λ L (· = q.v) → MovedTo (ofSplit q) V t β (F.β.submatrix id σ) → IntIn q V F N → GlobalTheory.FinPl.latV V L (· = q.v) = GlobalTheory.FinPl.latV V N (· = q.v) := by
  intro D V t Λ L N β k _ _ _ _ q Y _ _ F σ ht hΛ hβ hL hN hm hM hI
  have he := e_mem_intAt q

  have hw : ∀ z : Fin V.rank → AE D, q.e • z ∈ latV V L (· = q.v) ↔ q.e • z ∈ latV V N (· = q.v) := by
    intro z
    set y : Fin V.rank → k := fun i => q.pr (z i) with hydef
    have hz : q.e • z = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := by
      rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
      funext i
      simp only [hydef, q.sec_pr, Pi.smul_apply, smul_eq_mul]
    have hL' := sec_mem_iff V t Λ L β q (F.β.submatrix id σ) hβ hm hM ((F.γ *ᵥ y) ∘ σ)
    rw [Matrix.submatrix_mulVec_equiv] at hL'
    have e1 : ((F.γ *ᵥ y) ∘ σ) ∘ σ.symm = F.γ *ᵥ y := by
      funext i; simp
    rw [e1] at hL'
    rw [hz, ← hI]
    have e2 : (fun i => q.sec (((F.β *ᵥ (F.γ *ᵥ y)) ∘ id) i)) = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := rfl
    rw [e2] at hL'
    rw [hL']
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hherm : ∀ y x : Fin V.rank → AE D,
      GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) x = GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) (q.e • x) := by
    intro y x
    unfold GlobalTheory.IwaPlace.hermAt
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(cA D (x i) * gA V i j * y j)) * hce
  have hbar : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V B (· = q.v) → q.e • z ∈ latV V A (· = q.v)) →
      ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) →
        cA D q.e • z ∈ latV V A (· = q.v) → cA D q.e • z ∈ latV V B (· = q.v) := by
    intro A B hA hB hBA z hz h
    have hz' : ∀ i, (cA D q.e • z) i ∈ idAt D (· = q.v) := fun i => Ideal.mul_mem_left _ _ (hz i)
    refine ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V B q.v hB).2.2 _ hz').2 fun x hx => ?_
    rw [hherm]
    have hex : q.e • x ∈ latV V A (· = q.v) := hBA x (smul_mem_latV hB.1 hx he)
    exact ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V A q.v hA).2.2 _ hz').1 h _ hex
  have hsplit : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) → q.e • z + cA D q.e • z = z := by
    intro z hz
    obtain ⟨ε, hε, hs⟩ := q.above
    rw [← add_smul, hs]
    funext i
    exact ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 (z i)).1 (hz i)
  have hgen : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V A (· = q.v) ↔ q.e • z ∈ latV V B (· = q.v)) →
      latV V A (· = q.v) ≤ latV V B (· = q.v) := by
    intro A B hA hB hAB z hz
    have hs := GlobalTheory.FinPl.FrameLat.latV_supp hz
    have h1 : q.e • z ∈ latV V A (· = q.v) := smul_mem_latV hA.1 hz he
    have h3 : cA D q.e • z = z - q.e • z := by
      rw [eq_sub_iff_add_eq']
      exact hsplit z hs
    have h2 : cA D q.e • z ∈ latV V A (· = q.v) := by
      rw [h3]
      exact sub_mem hz h1
    have := add_mem ((hAB z).1 h1) (hbar A B hA hB (fun z => (hAB z).2) z hs h2)
    rwa [hsplit z hs] at this
  exact le_antisymm (hgen L N hL hN hw) (hgen N L hN hL fun z => (hw z).symm)

end GlobalTheory.SplitFrameLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulEqZeroOfNePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitOrth

theorem place_mul_place {D : D7} {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from FiniteAdeleRing.ext _ fun w => ?_)
  change evalV D.host.F w (α * β) = evalV D.host.F w 0
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

theorem split_mul_split : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' hv
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h1 : q.e * q.e = q.e := q.split.1
  have h2 : q.e * cA D q.e = 0 := q.split.2.1
  have h1' : q'.e * q'.e = q'.e := q'.split.1
  have h2' : q'.e * cA D q'.e = 0 := q'.split.2.1
  have a : q.e = q.e * algebraMap _ _ ε := by rw [← he, mul_add, h1, h2, add_zero]
  have a' : q'.e = q'.e * algebraMap _ _ ε' := by rw [← he', mul_add, h1', h2', add_zero]
  rw [a, a', mul_mul_mul_comm, ← map_mul, place_mul_place hε hε' hv, map_zero, mul_zero]

end GlobalTheory.SplitOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.OutsideOrth

theorem mul_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D),
    PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  intro D k _ _ _ _ p P PP e hPP hp he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun P' hP' => ?_
  rw [mul_comm]
  exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split hp) hp (hes P' hP')
    (fun h => hPP (h ▸ hP'))

end GlobalTheory.LocMod.OutsideOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → (IsSplit (E := D.host.E) v ↔ Formalism.DivisionValues.conjPl w ≠ w) ∧ (∀ χ : (AE D)ˣ →* Circle, (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ) ∧ (∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f) ∧ (IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.PlaceDict.dictionary | exact GlobalTheory.PlaceDict.dictionary | (intros; apply GlobalTheory.PlaceDict.dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.LocMod.Place

theorem intInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'],
    Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  intro k _ _ _ _ Y Y' _ _ _ _
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  set K : Set (Matrix Y Y' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hK
  have hKeq : K = Set.univ.pi fun _ : Y => Set.univ.pi fun _ : Y' => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ r) q (Set.mem_univ q)⟩
  have hKo : IsOpen K := by
    rw [hKeq]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hKc : IsCompact K := by
    rw [hKeq]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  have hcl : IsClosed K := by
    rw [hKeq]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (Valuation.isClosed_integer (v := valuation k))
  refine ⟨?_, ?_⟩
  · show IsLocallyConstant (K.indicator fun _ => (1 : ℂ))
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · show HasCompactSupport (K.indicator fun _ => (1 : ℂ))
    exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LocMod.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SplitProj

open Formalism.IndefR.Datum Formalism.L2.Theta

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (n : ℕ) :
    ∃ k : F, Valued.v (c - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set r : v.adicCompletion F := algebraMap F _ (π ^ n) with hr_def
  have hr : Valued.v r = WithZero.exp (-(n : ℤ)) := by
    rw [hr_def]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (π ^ n)).trans ?_
    rw [map_pow, hπ]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hr0 : Valued.v r ≠ 0 := by rw [hr]; exact WithZero.exp_ne_zero
  have hN : {y : v.adicCompletion F | Valued.v (c - y) < Valued.v r} ∈ nhds c := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict r)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => c - y)
    simp only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (c - c) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hr0
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hN
  exact ⟨k, (le_of_lt hk).trans_eq hr⟩

theorem afIso_one_tmul_apply (a : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P = GlobalTheory.AdeleBaseChange.adMap F E a P := by
  have key : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≤
      WithZero.exp (-(n : ℤ)) := fun n => by
    obtain ⟨k, hk⟩ := exists_near (P.under (𝓞 F)) (a (P.under (𝓞 F))) n
    have h1 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n hk
    have h2 : Valued.v (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) ≤
        WithZero.exp (-(n : ℤ)) := by
      rw [GlobalTheory.AdeleBaseChange.adMap_apply, ← GlobalTheory.AdeleBaseChange.locMap_algebraMap, ← map_sub]
      exact GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk
    have e : GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P =
        (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) -
          (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 h2)
  by_contra hne
  have h0 : Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := key (1 - WithZero.log (Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P -
    GlobalTheory.AdeleBaseChange.adMap F E a P))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

end Base

variable {D : Formalism.BasicNotions.D7}

theorem toAd_eq_afIso (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.toAd D w = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x a =>
    rw [GlobalTheory.StdFrames.toAd_spec]
    have e : (x ⊗ₜ[D.host.F] a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, GlobalTheory.Mem.Col2.afIso_tmul_one]
    congr 1
    exact FiniteAdeleRing.ext _ fun P => (afIso_one_tmul_apply a P).symm
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem cpt_eq_adAt (Q : HeightOneSpectrum (𝓞 D.host.E)) (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.cpt Q w = GlobalTheory.Mem.Col2.adAt D.host.F Q w := by
  show Formalism.UG.evalV D.host.E Q (GlobalTheory.StdFrames.toAd D w) = Formalism.UG.evalV D.host.E Q (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w)
  rw [toAd_eq_afIso]

theorem pr_eq_of_adAt : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  intro D k _ _ _ _ q PP he z x hz
  have hx : GlobalTheory.StdFrames.cpt PP (toEAf D (incA D x)) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)
  have hz' : GlobalTheory.StdFrames.cpt PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans hz
  have h1 : toEAf D (q.e * z) = toEAf D (q.e * incA D x) := by
    rw [RingHom.map_mul, RingHom.map_mul]
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hQ : Q = PP
    · rw [hQ, hx, hz']
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]
  have h2 : q.pr (q.e * z - q.e * incA D x) = 0 :=
    q.pr_eq_zero_of_toEAf he _ (by rw [RingHom.map_sub, h1, sub_self])
  rw [RingHom.map_sub, sub_eq_zero, ← q.sec_pr, ← q.sec_pr, q.pr_sec, q.pr_sec] at h2
  exact h2

end GlobalTheory.SplitProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempoten
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.AdForm

def intVecSub (D : D7) (n : ℕ) : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun {x y} hx hy k => (hx k).add (hy k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c {x} hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact c.2.mul (hx k)

theorem coe_intVecSub (D : D7) (n : ℕ) : ((intVecSub D n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := rfl

theorem stdHom_map_splitIdem : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  intro D S T a ha u hu
  have h := Formalism.IndefR.Fin.latO_map_splitIdem S T (intVecSub D S.rank) (intVecSub D T.rank) ha
    (u := u) (by rw [coe_intVecSub, coe_intVecSub]; exact hu)
  rw [coe_intVecSub, coe_intVecSub] at h
  exact h

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_decomposition : GlobalTheory.Published.StrongApproxSU → ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → ∀ g ∈ GfC V, ∃ r s k, IsRatFin V r ∧ s ∈ splitPart V ∧ k ∈ GfC V ∧ Moves V hn k (Formalism.L2.Col.stdLat D.host.E n) ∧ g = r * s * k := by
  first | exact @GlobalTheory.SplitDec.exists_rat_split_stab | exact GlobalTheory.SplitDec.exists_rat_split_stab | (intros; apply GlobalTheory.SplitDec.exists_rat_split_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillWittDecompositionStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kill_witt_decomposition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), P ≠ 0 → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (regRes omh mW θ τ d₀ b' zH P φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  first | exact @GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero | exact GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero | (intros; apply GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainStep_exact_innerProduct : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  first | exact @GlobalTheory.ChainTw.ExactNS.stepExactNS | exact GlobalTheory.ChainTw.ExactNS.stepExactNS | (intros; apply GlobalTheory.ChainTw.ExactNS.stepExactNS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugateStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_vector_rows_conjugate : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ ThetaLiftSpaceZero W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  first | exact @GlobalTheory.MiTop.unit_vector_line_conjugate | exact GlobalTheory.MiTop.unit_vector_line_conjugate | (intros; apply GlobalTheory.MiTop.unit_vector_line_conjugate <;> assumption)
end

