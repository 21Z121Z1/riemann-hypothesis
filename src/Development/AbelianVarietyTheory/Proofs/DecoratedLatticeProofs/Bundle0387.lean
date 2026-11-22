import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLattice
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollect
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CollectComb

theorem foldr_comp_eq {ι X : Type} (c o : ι → X → X) (hc : ∀ a b, a ≠ b → ∀ x, c a (o b x) = o b (c a x)) :
    ∀ (l : List ι), l.Nodup → ∀ F : X,
      l.foldr (fun i g => c i (o i g)) F = l.foldr (fun i g => c i g) (l.foldr (fun i g => o i g) F) := by
  have hpast : ∀ (b : ι) (t : List ι), b ∉ t → ∀ x,
      o b (t.foldr (fun i g => c i g) x) = t.foldr (fun i g => c i g) (o b x) := by
    intro b t hb x
    induction t with
    | nil => rfl
    | cons a t ih =>
      have hab : a ≠ b := fun h => hb (h ▸ List.mem_cons_self)
      have hbt : b ∉ t := fun h => hb (List.mem_cons_of_mem _ h)
      simp only [List.foldr_cons]
      rw [← ih hbt, hc a b hab]
  intro l hl F
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    rw [ih hl.2, hpast a t hl.1]

end GlobalTheory.CollectComb

theorem GlobalTheory.CollectComb.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  intro D ψ hψ S T M M' hM hM' n L hinj F
  have hat : ∀ i, GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).e ∧ GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).o := fun i =>
    ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).e_is.1 u hu),
     fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).o_at u hu)⟩
  refine GlobalTheory.CollectComb.foldr_comp_eq (fun i g => comb ψ S T (L i).e g) (fun i g => comb ψ S T (L i).o g) ?_ _
    (List.nodup_finRange n) F
  intro a b hab x
  have hdisj : ∀ p, p = (L a).q.v → ¬ p = (L b).q.v := fun p ha hb => hab (hinj (ha.symm.trans hb))
  exact (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).1 _ _ (hat a).1 (hat b).2 x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_fixes_latticeVacuum_periodLattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v → ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := by
  first | exact @GlobalTheory.LatSign.latSign | exact GlobalTheory.LatSign.latSign | (intros; apply GlobalTheory.LatSign.latSign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomAtIffLocPPerO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HomAtPer

theorem exists_den_away (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ z : 𝓞 D.host.E, z ∉ P.asIdeal ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * z := by
  haveI := P.isPrime
  have : Finite (𝓞 D.host.E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hl : (ringChar (𝓞 D.host.E ⧸ P.asIdeal)).Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ P.asIdeal) _
  have hlP : ((ringChar (𝓞 D.host.E ⧸ P.asIdeal) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _
  have h2 : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_right _ h))
  have hq : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ h))
  exact GlobalTheory.AAUnitAway.exists_den D P.asIdeal hl (UpperTheory.Ram.notMem_small_of_QS_notMem D.host hlP h2)
    (fun e => hq (e ▸ hlP)) hlP

theorem homAt_iff_locP_perO : ∀ (D : D7) (S T : HSp D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, x ∈ Formalism.L2.Col.homAt SS N N' ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D S T SS hSS N N' hN _hN' x
  constructor
  · intro hx P hP
    haveI := P.isPrime
    obtain ⟨gens, hgens⟩ := hN.1.fg
    have hden : ∀ g ∈ gens, ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x g ∈ N' := by
      intro g hg
      have hg' : g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
        ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul, ← hgens]; exact Submodule.subset_span hg⟩
      obtain ⟨s, hs, hsx⟩ := hx P hP g hg'
      exact ⟨s, hs, hsx⟩
    choose! sg hsg using hden
    set s : 𝓞 D.host.E := ∏ g ∈ gens, sg g with hs
    have hsP : s ∉ P.asIdeal := by
      rw [hs]
      intro hm
      obtain ⟨g, hg, hgP⟩ := Ideal.IsPrime.prod_mem_iff.1 hm
      exact (hsg g hg).1 hgP
    have hsx : s • x ∈ homO N N' := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        have e : (s • x) g = (∏ g' ∈ gens.erase g, sg g') • (sg g • x g) := by
          rw [LinearMap.smul_apply, smul_smul, hs, ← Finset.mul_prod_erase gens sg hg, mul_comm]
        rw [e]; exact N'.smul_mem _ (hsg g hg).2
      | zero => rw [map_zero]; exact N'.zero_mem
      | add y z _ _ h1 h2 => rw [map_add]; exact N'.add_mem h1 h2
      | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem _ h
    exact ⟨s, hsP, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, s • x, hsx, (one_smul _ _).symm⟩⟩
  · intro hx P hP y hy
    haveI := P.isPrime
    obtain ⟨z, hz, hden⟩ := exists_den_away D P (hSS P hP)
    obtain ⟨s, hs, hsx⟩ := hx P hP
    obtain ⟨t, ht, hty⟩ := hy
    have hper : ∀ w ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∀ v ∈ N, (z • w) v ∈ N' := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨r, hr, h0, hh0, rfl⟩ := h
        intro v hv
        obtain ⟨ρ, hρ⟩ := hden r hr
        have e : (z • r • h0) v = ρ • h0 v := by
          rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul D.host.E z, ← algebraMap_smul D.host.E ρ, smul_smul]
          congr 1
          change (z : D.host.E) * r = (ρ : D.host.E)
          rw [hρ, mul_comm]
        rw [e]; exact N'.smul_mem ρ (hh0 v hv)
      | zero => intro v _; rw [smul_zero, LinearMap.zero_apply]; exact N'.zero_mem
      | add w₁ w₂ _ _ h1 h2 => intro v hv; rw [smul_add, LinearMap.add_apply]; exact N'.add_mem (h1 v hv) (h2 v hv)
      | smul r w₁ _ h1 => intro v hv; rw [smul_comm, LinearMap.smul_apply]; exact N'.smul_mem r (h1 v hv)
    refine ⟨z * s * t, P.asIdeal.primeCompl.mul_mem (P.asIdeal.primeCompl.mul_mem hz hs) ht, ?_⟩
    have e : (z * s * t) • x y = (z • s • x) (t • y) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul, smul_smul]
      congr 1; ring
    rw [e]
    exact hper _ hsx _ hty

end GlobalTheory.HomAtPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeAtPlaces_congr_localLattices : ∀ (D : D7) (S T : HSp D) (N M : Lat S) (N' M' : Lat T), IsSelfDualC S N → IsSelfDualC S M → IsSelfDualC T N' → IsSelfDualC T M' → ∀ (P : Pl D → Prop), (∀ p, P p → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) → latO S T (N : Set _) (N' : Set _) P = latO S T (M : Set _) (M' : Set _) P := by
  first | exact @GlobalTheory.FinPl.LatCong.latO_congr | exact GlobalTheory.FinPl.LatCong.latO_congr | (intros; apply GlobalTheory.FinPl.LatCong.latO_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ M : ℕ, 0 < M → ∀ w : WO S T, IsHalf e w → ∃ (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ w = z.map (fun r => e * incA D r) + M • v := by
  first | exact @GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul | exact GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul | (intros; apply GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentHalf_mem_completedHomLattice_iff_local : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  first | exact @GlobalTheory.AdForm.HalfLat.half_mem_latO_iff | exact GlobalTheory.AdForm.HalfLat.half_mem_latO_iff | (intros; apply GlobalTheory.AdForm.HalfLat.half_mem_latO_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumPartialProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PartialIdemSum

theorem mul_sum_of_isIdemAt {D : D7} {x : AE D} {P : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x P) (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P' ∈ S, Formalism.L2.NTheta.IsIdemAt (f P') P') :
    x * ∑ P' ∈ S, f P' = if P ∈ S then x else 0 := by
  rw [Finset.mul_sum]
  split_ifs with hP
  · rw [Finset.sum_eq_single P]
    · have h1 := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P) P P hx (hf P hP)).1 rfl
      rw [← h1]; exact hx.1.1
    · intro P' hP' hne
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 (Ne.symm hne)
    · intro h; exact absurd hP h
  · refine Finset.sum_eq_zero fun P' hP' => ?_
    refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 ?_
    rintro rfl; exact hP hP'

theorem sum_mul_sum_of_subset {D : D7} (S S' : Finset (Formalism.L2.DIV.Pl D.host.E)) (f g : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) (hg : ∀ P ∈ S', Formalism.L2.NTheta.IsIdemAt (g P) P) (hS : S ⊆ S') :
    (∑ P ∈ S, f P) * ∑ P ∈ S', g P = ∑ P ∈ S, f P := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [mul_sum_of_isIdemAt (hf P hP) S' g hg, if_pos (hS hP)]

theorem sum_mul_of_not_mem {D : D7} (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) {x : AE D} {R : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x R) (hR : R ∉ S) : (∑ P ∈ S, f P) * x = 0 := by
  rw [mul_comm, mul_sum_of_isIdemAt hx S f hf, if_neg hR]

theorem partial_sums : ∀ (D : D7) (P₀ ι : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D) (es : ι → AE D),
    Disjoint P₀ ι → (∀ PP, Formalism.L2.NTheta.IsIdemAt (es PP) PP.1) → IsIdemSum e P₀ → IsIdemSum e' (P₀ ∪ ι) →
    e' * e' = e' ∧ ∀ Q : Finset ι, IsIdemSum (e + ∑ PP ∈ Q, es PP) (P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι))) ∧
      (e + ∑ PP ∈ Q, es PP) * (e + ∑ PP ∈ Q, es PP) = e + ∑ PP ∈ Q, es PP ∧
      (e + ∑ PP ∈ Q, es PP) * e' = e + ∑ PP ∈ Q, es PP ∧
      ∀ R, R ∉ Q → (e + ∑ PP ∈ Q, es PP) * es R = 0 := by
  intro D P₀ ι e e' es hdisj hes he he'
  obtain ⟨⟨es₀, hes₀, rfl⟩, -⟩ := he
  obtain ⟨⟨es'', hes'', rfl⟩, hce'⟩ := he'
  set g : Formalism.L2.DIV.Pl D.host.E → AE D :=
    fun P => if P ∈ P₀ then es₀ P else if h : P ∈ ι then es ⟨P, h⟩ else 0 with hgdef
  have hg : ∀ P ∈ P₀ ∪ ι, Formalism.L2.NTheta.IsIdemAt (g P) P := by
    intro P hP
    by_cases h0 : P ∈ P₀
    · simp only [hgdef, if_pos h0]; exact hes₀ P h0
    · have hι : P ∈ ι := by
        rcases Finset.mem_union.mp hP with h | h
        · exact absurd h h0
        · exact h
      simp only [hgdef, if_neg h0, dif_pos hι]; exact hes ⟨P, hι⟩
  refine ⟨sum_mul_sum_of_subset _ _ es'' es'' hes'' hes'' subset_rfl, fun Q => ?_⟩
  have hmapι : Q.map (Function.Embedding.subtype (· ∈ ι)) ⊆ ι := by
    intro P hP
    obtain ⟨PP, -, rfl⟩ := Finset.mem_map.mp hP
    exact PP.2
  have hS : P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)) ⊆ P₀ ∪ ι :=
    Finset.union_subset_union subset_rfl hmapι
  have hgS : ∀ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), Formalism.L2.NTheta.IsIdemAt (g P) P :=
    fun P hP => hg P (hS hP)
  have hsum : ∑ P ∈ P₀, es₀ P + ∑ PP ∈ Q, es PP =
      ∑ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), g P := by
    rw [Finset.sum_union (Finset.disjoint_of_subset_right hmapι hdisj), Finset.sum_map]
    congr 1
    · refine Finset.sum_congr rfl fun P hP => ?_
      simp only [hgdef, if_pos hP]
    · refine Finset.sum_congr rfl fun PP _ => ?_
      have hn : (PP : Formalism.L2.DIV.Pl D.host.E) ∉ P₀ := Finset.disjoint_right.mp hdisj PP.2
      simp only [hgdef, Function.Embedding.coe_subtype, if_neg hn, dif_pos PP.2]
  rw [hsum]
  have hxy := sum_mul_sum_of_subset _ _ g es'' hgS hes'' hS
  refine ⟨⟨⟨g, hgS, rfl⟩, ?_⟩, sum_mul_sum_of_subset _ _ g g hgS hgS subset_rfl, hxy, fun R hR => ?_⟩
  · set x := ∑ P ∈ P₀ ∪ Q.map (Function.Embedding.subtype (· ∈ ι)), g P
    set y := ∑ P ∈ P₀ ∪ ι, es'' P
    calc x * cA D x = (x * y) * cA D (x * y) := by rw [hxy]
      _ = (x * cA D x) * (y * cA D y) := by rw [map_mul]; ring
      _ = 0 := by rw [hce', mul_zero]
  · refine sum_mul_of_not_mem _ g hgS (hes R) ?_
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.disjoint_left.mp hdisj h R.2
    · obtain ⟨PP, hPP, hPR⟩ := Finset.mem_map.mp h
      have : PP = R := Subtype.ext hPR
      exact hR (this ▸ hPP)

end GlobalTheory.PartialIdemSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  first | exact @GlobalTheory.LatIndSB.indicator_latO_mem_SB | exact GlobalTheory.LatIndSB.indicator_latO_mem_SB | (intros; apply GlobalTheory.LatIndSB.indicator_latO_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitUpStd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul' (q : GlobalTheory.FinPl.SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

set_option maxHeartbeats 800000 in
theorem int_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  intro D k _ _ _ _ q S T a₀ ha₀ _ FS FT hβ _ hγ t ht
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]

  let G : Fin T.rank → Fin S.rank → WO S T := fun i l =>
    Matrix.of fun i' j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)
  have hsingle : ∀ (n : ℕ) (l : Fin n), (Pi.single l (1 : D.host.E) : Fin n → D.host.E) ∈ intVecSub D n := by
    intro n l m
    by_cases hm : m = l
    · subst hm; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hm]; exact isIntegral_zero
  have hG : ∀ i l, G i l ∈ stdHom S T := fun i l =>
    Formalism.IndefR.Fin.gen_mem S T (intVecSub D S.rank) (intVecSub D T.rank) hα ha₀ (hsingle _ l) (hsingle _ i)
  have htm : ∀ (x : k) (y : D.host.E), q.sec x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) = q.sec (x * q.pr (incA D y)) := by
    intro x y
    have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] y = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D y := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have h2 : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
    rw [e1, ← mul_assoc, ← h2, mul_assoc q.e, mul_comm (q.sec x), ← mul_assoc q.e, hee, h2, sec_mul']
  have hrow : ∀ (l : Fin S.rank) j,
      ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j = S.gram l j := by
    intro l j
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, star_one, one_mul]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hGapp : ∀ i l i' j, (q.sec (t i l) • G i l) i' j = q.sec (t i l) * (pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)) := fun _ _ _ _ => rfl
  have key : (Place.ofSplitPt q).up FS FT t = ∑ i, ∑ l, q.sec (t i l) • G i l := by
    ext i' j
    change q.sec ((FT.β * t * FS.γ) i' j) = _
    rw [hβ, hγ, Matrix.one_mul, Matrix.sum_apply, Finset.sum_eq_single i']
    · rw [Matrix.sum_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hGapp, htm, hrow, Pi.single_eq_same, mul_one, map_mul (incA D), map_mul q.pr, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    · intro i _ hi
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hGapp, Pi.single_eq_of_ne (Ne.symm hi), mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [key]
  refine sum_mem fun i _ => sum_mem fun l _ => ?_
  exact Formalism.IndefR.Fin.latO_smul_mem S T (intVecSub D S.rank) (intVecSub D T.rank) ((q.int_iff _).1 (ht i l)) (hG i l)

end GlobalTheory.SplitUpStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_tensorIntegralIndicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ, IsSBHalf e (stdHom S T) Φ → IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ (Place.intInd Y Y'))) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ (T' ∘ₗ p.tensorOne FS FT) := by
  first | exact @GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne | exact GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne | (intros; apply GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ → ∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ) := by
  first | exact @GlobalTheory.LocMod.Place.isSBHalf_tensorAt | exact GlobalTheory.LocMod.Place.isSBHalf_tensorAt | (intros; apply GlobalTheory.LocMod.Place.isSBHalf_tensorAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratesSpanConsecutiveSpaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.SpanY

theorem itSpans_pk : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((pk W).MY j) ((pk W).MY (j + 1)) ((pk W).ItY j) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP j hj
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  obtain ⟨hw, hv⟩ := hok.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((pk W).MY j) ((pk W).MY (j + 1)) (pk W).θ (pk W).ψ _ _
    ((pk W).ωY W.P.A3.A.μ0 j) ((pk W).vY W.P.A3.A.μ0 j) ((pk W).ItY j) hC.models.inf hw hv (hC.chain.ItY W.P.A3.A.μ0 j hj)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((pk W).ItY j P) (Submodule.span ℂ
      {x | ∃ (P : PolF D (Yc D (j + 1)).rank (Yc D j).rank) (y : ((pk W).MY (j + 1)).Vec), KVecP ((pk W).MY (j + 1)) y ∧
        x = (pk W).ItY j P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Core.Mi.SpanY

end
end

