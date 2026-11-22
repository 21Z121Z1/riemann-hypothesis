import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerFormValueStep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralAdeleIffBothComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_integralAdele_iff_both_components : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D), a ∈ GlobalTheory.FinPl.idAt D (· = q.v) → (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.SplitInt.intAt_iff_pr | exact GlobalTheory.SplitInt.intAt_iff_pr | (intros; apply GlobalTheory.SplitInt.intAt_iff_pr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section
namespace GlobalTheory.PhiOneVal

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_last_of_pair {a : ℕ} (Q : Pair k (Fin a)) : ∃ r : Fin a, r.1 + 1 = a := by
  rcases a with _ | a
  · exact absurd (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]) Q.fn_ne
  · exact ⟨Fin.last a, rfl⟩

theorem hasVal_finset_sum {n ι : Type} (Q : Pair k n) (s : Finset ι) (x : ι → n → k) (v : ι → 𝓀[k])
    (h : ∀ i, Q.HasVal (x i) (v i)) : Q.HasVal (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Pair.mem_ker.1 (zero_mem Q.ker)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem maps_iff_basis {n n' : Type} [Fintype n] [DecidableEq n] (Q : Pair k n) (Q' : Pair k n') (A A' : Matrix n n k)
    (hA : A' * A = 1) (hQ : ∀ x ∈ Q.lat, ∀ r, (A *ᵥ x) r ∈ 𝒪[k]) (v : n → 𝓀[k])
    (hv : ∀ r, Q.HasVal (A' *ᵥ Pi.single r 1) (v r)) (M : Matrix n' n k) :
    Maps Q Q' M ↔ ∀ r, Q'.HasVal (M *ᵥ (A' *ᵥ Pi.single r 1)) (v r) := by
  rw [maps_iff_hasVal]
  refine ⟨fun h r => h _ _ (hv r), fun h y c hy => ?_⟩
  let w : n → 𝒪[k] := fun r => ⟨_, hQ y hy.mem r⟩
  have e : y = ∑ r, w r • (A' *ᵥ Pi.single r 1) := by
    have e1 : A *ᵥ y = ∑ r, w r • (Pi.single r 1 : n → k) := by
      ext i
      simp [w, Pi.single_apply, Finset.sum_apply, Subring.smul_def]
    calc y = A' *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec, hA, one_mulVec]
      _ = _ := by
        rw [e1, mulVec_sum]
        exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _
  have h1 := hasVal_finset_sum Q Finset.univ _ _ fun r => (hv r).smul (w r)
  have h2 := hasVal_finset_sum Q' Finset.univ _ _ fun r => (h r).smul (w r)
  rw [← e] at h1
  rw [hy.unique h1]
  convert h2 using 1
  conv_lhs => rw [e, mulVec_sum]
  exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* k) (ψ : 𝓞 E →+* 𝒪[k])

theorem hasVal_col_iff (hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 E) E c))
    (hres : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal)
    (hint : ∀ x : E, φ x ∈ 𝒪[k] → ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E s * x)
    {b : ℕ} (Q : Pair k (Fin b)) (B B' : Matrix (Fin b) (Fin b) k) (hB : B * B' = 1)
    (hQ : ∀ x ∈ Q.lat, ∀ r, (B *ᵥ x) r ∈ 𝒪[k]) (t : 𝓞 E)
    (hv : ∀ w : Fin b → 𝓞 E, ∀ r : Fin b, r.1 + 1 = b →
      Q.HasVal (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (w r'))) (residue 𝒪[k] (ψ (t * w r))))
    (u : Fin b → E) (ε : 𝓞 E) :
    Q.HasVal (B' *ᵥ fun q => φ (u q)) (residue 𝒪[k] (ψ (t * ε))) ↔
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E, (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) ∧
        ∀ q : Fin b, q.1 + 1 = b → t * (c q - s * ε) ∈ P.asIdeal := by
  have key : ∀ (s : 𝓞 E) (c : Fin b → 𝓞 E), (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) →
      (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (c r'))) = ψ s • (B' *ᵥ fun q => φ (u q)) := by
    intro s c hc
    rw [← mulVec_smul]
    congr 1
    ext q
    rw [hc, map_mul, ← hψ]
    rfl
  have key2 : ∀ s c : 𝓞 E, t * (c - s * ε) ∈ P.asIdeal ↔
      residue 𝒪[k] (ψ (t * c)) = residue 𝒪[k] (ψ s) * residue 𝒪[k] (ψ (t * ε)) := by
    intro s c
    rw [← hres, ← map_mul, ← map_mul, show t * (c - s * ε) = t * c - s * (t * ε) by ring, map_sub, map_sub, sub_eq_zero]
  constructor
  · intro h
    have h1 := hQ _ h.mem
    rw [mulVec_mulVec, hB, one_mulVec] at h1
    choose s hs c hc using fun q => hint _ (h1 q)
    have hc' : ∀ q, algebraMap (𝓞 E) E (c q * ∏ q' ∈ Finset.univ.erase q, s q') =
        algebraMap (𝓞 E) E (∏ q', s q') * u q := by
      intro q
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q), map_mul, map_mul, hc]
      ring
    refine ⟨∏ q, s q, ?_, fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q', hc', fun q hq => ?_⟩
    · haveI := P.isPrime
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨q, -, hq⟩
      exact hs q hq
    · rw [key2]
      have h2 := hv (fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q') q hq
      rw [key _ _ hc'] at h2
      exact h2.unique (h.smul _)
  · rintro ⟨s, hs, c, hc, hP⟩
    obtain ⟨q, hq⟩ := exists_last_of_pair Q
    have h2 := hv c q hq
    rw [key _ _ hc, (key2 _ _).1 (hP q hq)] at h2
    obtain ⟨v, hv'⟩ : IsUnit (ψ s) := by
      by_contra hn
      exact hs ((hres s).1 ((residue_eq_zero_iff _).2 hn))
    have h3 := h2.smul (↑v⁻¹ : 𝒪[k])
    rwa [← hv', smul_smul, Units.inv_mul, one_smul, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h3

end Local

theorem maps_rd_iff_colCond : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  intro D k _ _ _ _ p P hP S T a b hS hT α β Q Q' LS LT t hLS hLT hα hβ vS vT z
  subst hS hT
  let φ : D.host.E →+* k := p.pr.comp (incA D)
  have hres := GlobalTheory.T.split_component_integer_residue_zero_iff_mem_prime p P hP
  let ψ : 𝓞 D.host.E →+* 𝒪[k] := (φ.comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _ fun c => (hres c).1
  have hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 D.host.E) D.host.E c) := fun c => rfl
  have hres' : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal := fun c => (hres c).2
  have hS : ∀ w : Fin S.rank → 𝓞 D.host.E, ∀ r : Fin S.rank, r.1 + 1 = S.rank →
      Q.HasVal (α.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vS (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLS _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  have hT : ∀ w : Fin T.rank → 𝓞 D.host.E, ∀ r : Fin T.rank, r.1 + 1 = T.rank →
      Q'.HasVal (β.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vT (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLT _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  obtain ⟨l, hl⟩ := exists_last_of_pair Q
  have hy : ∀ r : Fin S.rank, Q.HasVal (α.b' *ᵥ Pi.single r 1)
      (residue 𝒪[k] (ψ (t * if r.1 + 1 = S.rank then 1 else 0))) := by
    intro r
    have h := hS (Pi.single r 1) l hl
    have e1 : (fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E ((Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) r'))) =
        Pi.single r 1 := by
      ext r'
      by_cases h' : r' = r <;> simp [Pi.single_apply, h']
    have e2 : (Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) l = if r.1 + 1 = S.rank then 1 else 0 := by
      rw [Pi.single_apply]
      exact if_congr ⟨fun h => h ▸ hl, fun h => Fin.ext (by omega)⟩ rfl rfl
    rwa [e1, e2] at h
  rw [maps_iff_basis Q Q' α.b α.b' α.b'b (fun x hx => (GlobalTheory.T.split_place_lattice_component_integral_frame_coords α LS Q.lat hα hLS x).1 hx) _ hy]
  refine forall_congr' fun r => ?_
  have e : GlobalTheory.FinPl.rd α β (z.map (incA D)) *ᵥ (α.b' *ᵥ Pi.single r 1) = β.b' *ᵥ fun q => φ (z q r) := by
    rw [GlobalTheory.FinPl.rd, mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one, ← mulVec_mulVec, mulVec_single_one]
    rfl
  rw [e, hasVal_col_iff P φ ψ hψ hres' (GlobalTheory.PhiOneVal.exists_denom_notMem_of_pr_int p P hP) Q' β.b β.b' β.bb'
    (fun x hx => (GlobalTheory.T.split_place_lattice_component_integral_frame_coords β LT Q'.lat hβ hLT x).1 hx) t hT]
  have e3 : ∀ q, toHom S T rfl rfl z (Pi.single r 1) q = z q r := by
    intro q
    simp [toHom]
  simp only [e3, mul_ite, mul_one, mul_zero]

end GlobalTheory.PhiOneVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLineSim

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_not_int : ∃ x : k, x ∉ 𝒪[k] := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r⁻¹, fun h => ?_⟩
  have h1 : valuation k r⁻¹ ≤ 1 := h
  have hr : r ≠ 0 := hr0
  have : (1 : ValueGroupWithZero k) ≤ valuation k r := by
    calc (1 : ValueGroupWithZero k) = valuation k (r * r⁻¹) := by rw [mul_inv_cancel₀ hr, map_one]
      _ = valuation k r * valuation k r⁻¹ := map_mul _ _ _
      _ ≤ valuation k r * 1 := by gcongr
      _ = valuation k r := mul_one _
  exact absurd hr1 (not_lt.2 this)

theorem mul_sec' (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm]

theorem mul_csec (q : SplitPt D k) (a : AE D) (b : k) :
    a * cA D (q.sec b) = cA D (q.sec (q.pr (cA D a) * b)) := by
  rw [← mul_sec', map_mul, Formalism.L2.Theta.cA_cA]

theorem mulVec_sec' (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (A : Fin n → k) :
    (M *ᵥ fun i => q.sec (A i)) = fun j => q.sec ((M.map q.pr *ᵥ A) j) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sec', map_sum]

theorem mulVec_csec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (B : Fin n → k) :
    (M *ᵥ fun i => cA D (q.sec (B i))) = fun j => cA D (q.sec ((M.map (fun a => q.pr (cA D a)) *ᵥ B) j)) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_csec, map_sum]

theorem pr_cA_sec (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
  have he : q.pr (cA D q.e) = 0 := by
    have h1 : q.pr (cA D q.e * q.e) = 0 := by rw [FrameLat.cAe_mul_e, map_zero]
    have pe : q.pr q.e = 1 := by rw [← FrameLat.sec_one, q.pr_sec]
    rwa [map_mul, pe, mul_one] at h1
  rw [← FrameLat.e_mul_sec q c, map_mul, map_mul, he, zero_mul]

theorem pr_cA_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := FrameLat.csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := (h.1 _ hc).1
  have h3 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1).1 h2).2
  rwa [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at h3

theorem pr_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (incA D D.host.xi0) ∈ 𝒪[k] :=
  (GlobalTheory.SplitIntComp.val_xi q h).le

end GlobalTheory.SplitLineSim

namespace GlobalTheory.SplitLineSim
open GlobalTheory.FinPl

theorem line_sim_maps : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  intro D k _ _ _ _ q L L'' τ LL LZ zL z₀ u hU hLL hLZ hr hr'' hcL hcZ hu hτz hτ y hy
  haveI : Unique (Fin L.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  haveI : Unique (Fin L''.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  set j0 : Fin L.rank := default with hj0
  set i0 : Fin L''.rank := default with hi0
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hu_int : u ∈ 𝒪[k] := hu.le
  have hui_int : u⁻¹ ∈ 𝒪[k] := by
    show valuation k u⁻¹ ≤ 1
    rw [map_inv₀, hu, inv_one]

  have h1 : q.pr (incA D (τ j0 i0)) * z₀ i0 = u * zL j0 := by
    have := congrFun hτz j0
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hzL : zL j0 ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_not_int (k := k)
    apply hx
    rw [hcL]
    have : (fun i => q.sec (zL i * x)) = 0 := by
      funext i
      rw [Subsingleton.elim i j0, h0, zero_mul, map_zero]
      rfl
    rw [this]
    exact zero_mem _
  have hz0 : z₀ i0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hzL ((mul_eq_zero.1 h1.symm).resolve_left hu0)

  have hyS : ∀ i, y i ∈ idAt D (· = q.v) := FrameLat.latV_supp hy
  set A : Fin L''.rank → k := fun i => q.pr (y i) with hA
  set B : Fin L''.rank → k := fun i => q.pr (cA D (y i)) with hB
  have hyAB : y = (fun i => q.sec (A i)) + fun i => cA D (q.sec (B i)) := by
    funext i
    exact GlobalTheory.SplitIntComp.eq_sec_add_csec q (hyS i)
  rw [hyAB] at hy
  obtain ⟨hyA, hyB⟩ := (FrameLat.decomp hLZ A B).1 hy
  rw [hyAB, Matrix.mulVec_add, mulVec_sec', mulVec_csec]
  refine (FrameLat.decomp hLL _ _).2 ⟨?_, ?_⟩
  ·
    set c : k := A i0 / z₀ i0 with hc
    have hcA : ∀ i, z₀ i * c = A i := fun i => by
      rw [Subsingleton.elim i i0, hc, mul_div_cancel₀ _ hz0]
    have hcint : c ∈ 𝒪[k] := (hcZ c).2 (by simpa only [hcA] using hyA)
    have : (fun j => q.sec ((((rat τ : Mx D L.rank L''.rank)).map q.pr *ᵥ A) j)) =
        fun j => q.sec (zL j * (u * c)) := by
      funext j
      rw [Subsingleton.elim j j0]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rw [← hcA i0]
      change q.pr (incA D (τ j0 i0)) * (z₀ i0 * c) = _
      rw [← mul_assoc, h1]
      ring
    rw [this]
    exact (hcL _).1 (mul_mem hu_int hcint)
  ·
    rw [FrameLat.csec_mem_iff hLL]
    intro x hx
    have h00 : star (τ j0 i0) * (L.gram j0 j0 * τ j0 i0) = -(D.host.xi0 * star D.host.xi0) * L''.gram i0 i0 := by
      have := congrFun (congrFun hτ i0) i0
      rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique,
        Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
    let φ : D.host.E →+* k := (q.pr.comp (cA D)).comp (incA D)
    have hφs : ∀ t : D.host.E, φ (star t) = q.pr (incA D t) := fun t => by
      show q.pr (cA D (incA D (star t))) = _
      rw [FrameLat.cA_incA, star_star]

    have e3 : q.pr (incA D (τ j0 i0)) * (q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0)))) =
        -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) * q.pr (cA D (incA D (L''.gram i0 i0))) := by
      have h2 := congrArg φ h00
      rw [map_mul, map_mul, map_mul, map_neg, map_mul, hφs (τ j0 i0), hφs D.host.xi0] at h2
      exact h2
    have hcw_int : -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) ∈ 𝒪[k] :=
      neg_mem (mul_mem (pr_cA_xi_int q hU) (pr_xi_int q hU))
    obtain ⟨c', hc'⟩ : ∃ c' : k, c' = x j0 / zL j0 := ⟨_, rfl⟩
    have hxc : ∀ j, zL j * c' = x j := fun j => by
      rw [Subsingleton.elim j j0, hc', mul_div_cancel₀ _ hzL]
    have hc'int : c' ∈ 𝒪[k] := (hcL c').2 (by simpa only [hxc] using hx)

    have hz1 : (fun i => q.sec (z₀ i)) ∈ latV L'' LZ (· = q.v) := by
      simpa only [mul_one] using (hcZ 1).1 (one_mem _)
    have hZB := (FrameLat.csec_mem_iff hLZ B).1 hyB z₀ hz1
    simp only [Fintype.sum_unique] at hZB
    have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    have e0 : ((((rat τ : Mx D L.rank L''.rank)).map (fun a => q.pr (cA D a)) *ᵥ B) j0) =
        q.pr (cA D (incA D (τ j0 i0))) * B i0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rfl
    simp only [Fintype.sum_unique]
    rw [e0, ← hxc j0]
    have key : zL j0 * c' * q.pr (cA D (incA D (L.gram j0 j0))) * (q.pr (cA D (incA D (τ j0 i0))) * B i0) =
        c' * u⁻¹ * (-(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0))) *
          (z₀ i0 * q.pr (cA D (incA D (L''.gram i0 i0))) * B i0) := by
      linear_combination (c' * u⁻¹ * z₀ i0 * B i0) * e3 -
        (c' * u⁻¹ * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0) * h1 -
        (c' * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0 * zL j0) * hinv
    rw [key]
    exact mul_mem (mul_mem (mul_mem hc'int hui_int) hcw_int) hZB

end GlobalTheory.SplitLineSim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  first | exact @GlobalTheory.AdForm.OffPlace.map_pr_of_off | exact GlobalTheory.AdForm.OffPlace.map_pr_of_off | (intros; apply GlobalTheory.AdForm.OffPlace.map_pr_of_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  first | exact @GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | exact GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | (intros; apply GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceWPartFrameColumnMultipleMemIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_wPart_frameColumnMultiple_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (m₀ : Y) (c₀ : k), IntIn q S F L → valuation k c₀ = 1 → (∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) → ∀ a : AE D, ((fun r => q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr a ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.ColsWPart.wpart_mem_iff | exact GlobalTheory.ColsWPart.wpart_mem_iff | (intros; apply GlobalTheory.ColsWPart.wpart_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerFormValueStepStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_form_value_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ), i < B.R.m →
    ∀ (c : (I.stp u I.mu0 i).Cl) (c' : (I.stp u I.mu0 (i + 1)).Cl) (g : (I.stp u I.mu0 (i + 1)).Stab c')
      (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
      f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) →
      (I.stp u I.mu0 (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u I.mu0).Kmap i c c' f) = (I.chain l u I.mu0).Kmap i c c' f := by
  first | exact @GlobalTheory.KerStab.Kmap_stab | exact GlobalTheory.KerStab.Kmap_stab | (intros; apply GlobalTheory.KerStab.Kmap_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardDatum_splitPlaces_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := by
  first | exact @GlobalTheory.AdForm.stdT_levelPrime_mem_v | exact GlobalTheory.AdForm.stdT_levelPrime_mem_v | (intros; apply GlobalTheory.AdForm.stdT_levelPrime_mem_v <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}

theorem step_index_le_s (J : QJ a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  have h2 : (I.rec7 l Z).R.m = B.R.m := rfl
  omega

def phi (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := step_index_le_s J i hj; omega))

def H (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := step_index_le_s J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (step_index_le_s J i hj)) (α i)))

def twAt (J : QJ a t) : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop := fun v => ∃ i, (J.G i).q.v = v

def relax (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i => KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)).comap (phi J j hj)

def Up (a : GeoAll W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

theorem Up_le (a : GeoAll W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Up a j hj ≤ GfC _ := by
  unfold Up
  split_ifs
  · intro g hg
    exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  · exact bot_le

theorem wt_eq {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T} (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    (J.E i).wt j (α i) = ((((J.E i).m j (H J j hj α i)).toReal⁻¹ : ℝ) : ℂ) :=
  (J.E i).wt_mid j ((J.G i).s - j) (Nat.add_sub_cancel' (step_index_le_s J i hj)) (α i)
end GlobalTheory.LevProd
end
end

