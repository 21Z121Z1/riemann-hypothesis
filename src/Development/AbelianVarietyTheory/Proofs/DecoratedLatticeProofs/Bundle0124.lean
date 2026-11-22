import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarAdelicUpperUnitriangularEntryTranslateInvari
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
section
noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd Lifts InDual)

namespace GlobalTheory.FinPl.Comm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

open Classical in

theorem integral_vecInd_eq_zero [MeasurableSpace k] [BorelSpace k] (χ : AddChar k Circle) (e : k)
    (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) (η : n → k) {y₀ : n → k}
    (hy₀ : y₀ ∈ L) (hne : χ (e * (η ⬝ᵥ y₀)) ≠ 1) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) y₀
  have e2 : ∀ y, vecInd L (y + y₀) * (χ (e * (η ⬝ᵥ (y + y₀))) : ℂ) =
      (χ (e * (η ⬝ᵥ y₀)) : ℂ) * (vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) := fun y => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, vecInd, vecInd,
      if_congr (L.add_mem_iff_left hy₀) rfl rfl]
    ring
  simp only [e2] at h
  rw [integral_const_mul] at h
  by_contra h0
  exact hne (Circle.ext (by simpa using (mul_eq_right₀ h0).1 h))

theorem exists_lifts_value (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0)
    {F : n → k} (hF : Lifts L F f) (b : 𝓀[k]) :
    ∃ y₀ ∈ L, ∃ s : 𝒪[k], (s : k) = F ⬝ᵥ y₀ ∧ residue 𝒪[k] s = b := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨y, rfl⟩ := Red.mk_surjective L x
  obtain ⟨t, ht⟩ := residue_surjective (R := 𝒪[k]) (b * (f (Red.mk L y))⁻¹)
  obtain ⟨s, hs, hs'⟩ := hF (t • y)
  refine ⟨_, (t • y).2, s, hs, ?_⟩
  rw [hs', map_smul, ← Red.residue_smul, map_smul, ht, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem integral_vecInd_coset [MeasurableSpace k] [BorelSpace k] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (he : e = 1 ∨ e = -1) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0) {F η : n → k}
    (hF : Lifts L F f) (hη : InDual L (η - q.inv • F)) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, resChar χ hχ q a ≠ 1 := by
    by_contra h
    push Not at h
    exact resChar_ne_one hχ q (by ext a; rw [h a, AddChar.one_apply])
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have heo : e ∈ 𝒪[k] := by
    rcases he with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  let ε : 𝒪[k] := ⟨e, heo⟩
  have hε : residue 𝒪[k] ε * residue 𝒪[k] ε = 1 := by
    rw [← map_mul, show ε * ε = 1 from Subtype.ext hee, map_one]
  obtain ⟨y₀, hy₀, s, hs, hs'⟩ := exists_lifts_value L hf hF (residue 𝒪[k] ε * a)
  refine integral_vecInd_eq_zero χ e μ L η hy₀ fun h => ha ?_
  have hl : e * ((η - q.inv • F) ⬝ᵥ y₀) ∈ 𝒪[k] := mul_mem heo (hη y₀ hy₀)
  have hsplit : e * (η ⬝ᵥ y₀) = q.inv * ((ε * s : 𝒪[k]) : k) + e * ((η - q.inv • F) ⬝ᵥ y₀) := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, Subring.coe_mul, hs]
    change _ = _ * (e * _) + _
    ring
  rw [hsplit, AddChar.map_add_eq_mul, apply_int_eq_one hχ ⟨_, hl⟩, mul_one] at h
  rw [show a = residue 𝒪[k] (ε * s) by rw [map_mul, hs', ← mul_assoc, hε, one_mul], resChar_residue, h]
  rfl

end GlobalTheory.FinPl.Comm

namespace GlobalTheory.FinPl.Comm

theorem fpair_vecInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k],
    fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) =
      fpair χ e μ (vecInd L) (dualInd L) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ L _
  unfold fpair
  congr 1
  funext η
  rw [Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum, add_eq_left]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  have hL : Q.lat = L := mem_withLat.1 hQ
  classical
  unfold cosetInd
  split_ifs with h
  · obtain ⟨F, hF, hD⟩ := h
    have h0 := integral_vecInd_coset q χ hχ e he μ Q.lat Q.red_ne hF hD
    rw [hL] at h0
    rw [h0, zero_mul]
  · rw [mul_zero]

end GlobalTheory.FinPl.Comm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicator
section
noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts InDual)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetPairing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

theorem exists_lifts [DecidableEq n] (P : Pair k n) : ∃ F, Lifts P.lat F P.red := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  let b := Module.Free.chooseBasis 𝒪[k] P.lat
  let G : (n → k) →ₗ[k] k := (b.extendOfIsLattice k).constr k fun i => (g (b i) : k)
  have h1 : (G.restrictScalars 𝒪[k]) ∘ₗ P.lat.subtype = (Algebra.linearMap 𝒪[k] k) ∘ₗ g := b.ext fun i => by
    have := (b.extendOfIsLattice k).constr_basis k (fun i => (g (b i) : k)) i
    rw [Module.Basis.extendOfIsLattice_apply] at this
    exact this
  refine ⟨fun i => G (Pi.single i 1), fun y => ⟨g y, ?_, LinearMap.congr_fun hg y⟩⟩
  have h2 : G y = (g y : k) := LinearMap.congr_fun h1 y
  rw [← h2, LinearMap.pi_apply_eq_sum_univ G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem inDual_of_lifts (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F F' : n → k}
    (hF : Lifts L F f) (hF' : Lifts L F' f) : InDual L (q.inv • F - q.inv • F') := fun y hy => by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  obtain ⟨t, ht, hr'⟩ := hF' ⟨y, hy⟩
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, hr, hr', sub_self]))
  have hu' : (s : k) - t = q.1 * u := by exact_mod_cast congrArg Subtype.val hu
  rw [← smul_sub, smul_dotProduct, sub_dotProduct, ← hs, ← ht, hu', smul_eq_mul, Unif.inv,
    inv_mul_cancel_left₀ q.ne_zero]
  exact u.2

theorem cosetInd_add (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F : n → k}
    (hF : Lifts L F f) (η : n → k) : cosetInd q L f (η + q.inv • F) = dualInd L η := by
  classical
  refine if_congr ⟨?_, fun h => ⟨F, hF, by simpa using h⟩⟩ rfl rfl
  rintro ⟨F', hF', h⟩ y hy
  have := sub_mem (h y hy) (inDual_of_lifts q hF hF' y hy)
  rwa [← sub_dotProduct, show η + q.inv • F - q.inv • F' - (q.inv • F - q.inv • F') = η by abel] at this

variable {χ : AddChar k Circle} (hχ : HasConductor χ 1) {e : k}

include hχ in

theorem char_dual (he : e = 1 ∨ e = -1) {L : Submodule 𝒪[k] (n → k)} {η y : n → k} (hη : InDual L η) (hy : y ∈ L) :
    χ (e * (η ⬝ᵥ y)) = 1 := by
  rcases he with rfl | rfl
  · simpa using apply_int_eq_one hχ ⟨_, hη y hy⟩
  · simpa using apply_int_eq_one hχ (-⟨_, hη y hy⟩)

theorem char_coset (q : Unif k) {ε : 𝓀[k]ˣ} (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) {P : Pair k n} {F η y : n → k}
    (hF : Lifts P.lat F P.red) (hη : InDual P.lat η) (hy : y ∈ P.lat) :
    (χ (e * ((η + q.inv • F) ⬝ᵥ y)) : ℂ) = resChar χ hχ q (ε * P.ev y) := by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  have hr' : P.ev y = residue 𝒪[k] s := ((P.hasVal_fn ⟨y, hy⟩).ev_eq).trans hr.symm
  rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, char_dual hχ (he.imp And.left And.left) hη hy, one_mul,
    smul_dotProduct, ← hs, hr']
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [resChar_residue]
  · have := resChar_residue hχ q (-s)
    simpa using this.symm

theorem exists_char_ne (q : Unif k) {ε : 𝓀[k]ˣ} (hε : ε = 1 ∨ ε = -1) {Q Q'' : Pair k n} (h : Q''.lat = Q.lat)
    (hne : Q'' ≠ ε • Q) : ∃ y ∈ Q.lat, resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ≠ 1 := by
  have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨y, hy, hc⟩ : ∃ y ∈ Q.lat, -Q.ev y + ε * Q''.ev y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hne (Pair.ext fun x a => ?_)
    rw [Pair.dia_hasVal, hi]
    constructor
    · intro hx
      have hx' := h ▸ hx.mem
      have := hc x hx'
      rw [hx.ev_eq, neg_add_eq_zero] at this
      exact this ▸ Pair.hasVal_ev hx'
    · intro hx
      have := hc x hx.mem
      rw [hx.ev_eq, neg_add_eq_zero, Units.mul_right_inj] at this
      exact this ▸ Pair.hasVal_ev (h ▸ hx.mem)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 (resChar_ne_one hχ q)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (a * (-Q.ev y + ε * Q''.ev y)⁻¹)
  refine ⟨s • y, Q.lat.smul_mem s hy, ?_⟩
  rw [((Pair.hasVal_ev hy).smul s).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).smul s).ev_eq]
  convert ha using 2
  rw [← inv_mul_cancel_right₀ hc a, ← hs]
  ring

theorem fpair_charInd_cosetInd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ) (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (Q Q'' : Pair k n) (h : Q''.lat = Q.lat) :
    (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧
    (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  obtain ⟨F, hF⟩ := exists_lifts Q''
  have hε : ε = 1 ∨ ε = -1 := he.imp And.right And.right
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      ∫ η, (∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ) * dualInd Q.lat η ∂μ := by
    unfold fpair
    rw [← integral_add_right_eq_self _ (q.inv • F)]
    congr 1
    funext η
    rw [cosetInd_add q hF, h]
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · rw [char_coset hχ q he hF (h ▸ hη) (h ▸ hy), charInd, AddChar.map_add_eq_mul]
      ring
    · rw [charInd, vecInd, if_neg hy, mul_zero, zero_mul, zero_mul]
  rw [key]
  constructor
  · rintro rfl
    unfold fpair
    congr 1
    funext η
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · have h1 : Q.ev y = (ε⁻¹ : 𝓀[k]ˣ) * (ε • Q).ev y := (Pair.dia_hasVal.1 (Pair.hasVal_ev (P := ε • Q) hy)).ev_eq
      have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
      rw [hi] at h1
      rw [char_dual hχ (he.imp And.left And.left) hη hy, ← h1, neg_add_cancel]
      simp
    · rw [vecInd, if_neg hy, zero_mul, zero_mul]
  · intro hne
    obtain ⟨y₀, hy₀, hc⟩ := exists_char_ne hχ q hε h hne
    have e1 := integral_add_right_eq_self (μ := μ)
      (fun y => vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) y₀
    have e2 : ∀ y, vecInd Q.lat (y + y₀) * resChar χ hχ q (-Q.ev (y + y₀) + ε * Q''.ev (y + y₀)) =
        resChar χ hχ q (-Q.ev y₀ + ε * Q''.ev y₀) * (vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) := fun y => by
      by_cases hy : y ∈ Q.lat
      · rw [vecInd, vecInd, if_pos hy, if_pos (add_mem hy hy₀), one_mul, one_mul, ← AddChar.map_add_eq_mul,
          ((Pair.hasVal_ev hy).add (Pair.hasVal_ev hy₀)).ev_eq,
          ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).add (Pair.hasVal_ev (h ▸ hy₀ : y₀ ∈ Q''.lat))).ev_eq]
        congr 1
        ring
      · rw [vecInd, vecInd, if_neg hy, if_neg fun h' => hy ((Q.lat.add_mem_iff_left hy₀).1 h')]
        simp
    simp only [e2] at e1
    rw [integral_const_mul] at e1
    have h0 : ∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ = 0 := by
      by_contra h0
      exact hc ((mul_eq_right₀ h0).1 e1)
    simp [h0]

end GlobalTheory.FinPl.CosetPairing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndica
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

noncomputable section

namespace GlobalTheory.FinPl.Comm

theorem fpair_charInd_dualInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n),
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  set r := resChar χ hχ q with hr
  obtain ⟨a, ha⟩ : ∃ a, r a ≠ 1 := by
    by_contra h
    push_neg at h
    exact resChar_ne_one hχ q (by ext x; simpa using h x)
  obtain ⟨e₁, he₁⟩ := Q.exists_hasVal_one
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (-a)
  have hy₀ : Q.HasVal (s • e₁) (-a) := by simpa [hs] using he₁.smul s
  have hI : ∫ y, charInd r Q y ∂μ = 0 := by
    have h1 := integral_add_right_eq_self (μ := μ) (charInd r Q) (s • e₁)
    have h2 : ∀ y, charInd r Q (y + s • e₁) = r a * charInd r Q y := fun y => by
      by_cases hy : y ∈ Q.lat
      · have hyy : y + s • e₁ ∈ Q.lat := add_mem hy hy₀.mem
        rw [charInd, charInd, vecInd, vecInd, if_pos hy, if_pos hyy, ((Pair.hasVal_ev hy).add hy₀).ev_eq,
          neg_add, neg_neg, AddChar.map_add_eq_mul]
        ring
      · have hyy : y + s • e₁ ∉ Q.lat := fun h => hy (by simpa using sub_mem h hy₀.mem)
        rw [charInd, charInd, vecInd, vecInd, if_neg hy, if_neg hyy]
        simp
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    by_contra h0
    exact ha ((mul_eq_right₀ h0).1 h1)
  unfold fpair
  have hF : ∀ η, (∫ y, charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * dualInd Q.lat η = 0 := fun η => by
    by_cases hη : GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Q.lat η
    · rw [dualInd, if_pos hη, mul_one]
      have : (fun y => charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ)) = fun y => charInd r Q y := by
        funext y
        by_cases hy : y ∈ Q.lat
        · have hm : e * (η ⬝ᵥ y) ∈ 𝒪[k] := by
            rcases he with rfl | rfl
            · simpa using hη y hy
            · simpa using hη y hy
          rw [show χ (e * (η ⬝ᵥ y)) = 1 from apply_int_eq_one hχ ⟨_, hm⟩]
          simp
        · rw [charInd, vecInd, if_neg hy]
          simp
      rw [this, hI]
    · rw [dualInd, if_neg hη, mul_zero]
  simp only [hF, integral_zero]

end GlobalTheory.FinPl.Comm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeDatumMainPartMemSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum qvec)

namespace GlobalTheory.FinPl.Comm

theorem mainDatum_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n) : mainDatum q χ ε P Q ∈ SB (Matrix n n' k) := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0}
  have h : mainDatum q χ ε P Q = ∑ f' : {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0},
      χ (-((ε : 𝓀[k]) * f'.1 (qvec q P))) • phiOne (ofDual P.ker f') Q := by
    funext x
    rw [mainDatum, finsum_eq_sum_of_fintype, Finset.sum_apply]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun f' _ => Submodule.smul_mem _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)

end GlobalTheory.FinPl.Comm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedSplitPlaceLineCoordinateIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.GluedInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec' (p : SplitPt D k) {S : HSp D} (h : GA D S) (u : Fin S.rank → k) :
    mt S h *ᵥ (fun i => p.sec (u i)) = fun i => p.sec (((mt S h).map p.pr *ᵥ u) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec]

theorem cAe_smul (p : SplitPt D k) {r : ℕ} (z : Fin r → AE D) :
    cA D p.e • z = fun i => cA D (p.sec (p.pr (cA D (z i)))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, p.sec_pr, map_mul, cA_cA]

def form (p : SplitPt D k) (S : HSp D) (x w : Fin S.rank → k) : k :=
  ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * w j

theorem form_eq (p : SplitPt D k) (S : HSp D) (x : Fin S.rank → k) (c : Fin S.rank → D.host.E) :
    form p S x (fun j => p.pr (cA D (incA D (c j)))) =
      x ⬝ᵥ fun i => p.pr (incA D ((star (S.gram *ᵥ c)) i)) := by
  unfold form
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, map_sum, star_mul', map_mul]
  rfl

theorem row_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    star (S.gram *ᵥ vecB o ζ) ᵥ* o.iA = 0 ∧ star (S.gram *ᵥ vecB o ζ) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
  have hr : star (S.gram *ᵥ vecB o ζ) = star ζ ᵥ* (o.iBᴴ * S.gram) := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_mul, gram_conjTranspose]
  rw [hr]
  constructor
  · rw [Matrix.vecMul_vecMul, o.orth, Matrix.vecMul_zero]
  · rw [vecB, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem form_frame (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (hs : IsSumFrame B.o B.ζ β β₀) (y : n ⊕ Fin 1 → k) :
    form p B.V₀ (β₀.b *ᵥ y) (fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j))) =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := by
  obtain ⟨h1, h2⟩ := row_orth B.o B.ζ
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  set r := star (B.V₀.gram *ᵥ vecB B.o B.ζ) with hr
  change form p B.V₀ _ (fun j => p.pr (cA D (incA D (vecB B.o B.ζ j)))) = _
  rw [form_eq, ← hr, hs, Matrix.fromCols_mulVec, add_dotProduct]
  have hA : (⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) = 0 := by
    funext a
    have hm : B.o.jA.map p.pr = B.o.iA.map ι := by
      rw [OrthDec.jA, rat, Matrix.map_map]; rfl
    rw [hm, ← RingHom.map_vecMul, h1]
    simp
  have e1 : ((B.o.jA.map p.pr * β.b) *ᵥ (y ∘ Sum.inl)) ⬝ᵥ (fun i => p.pr (incA D (r i))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
    change ((⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) ᵥ* β.b) ⬝ᵥ _ = 0
    rw [hA, Matrix.zero_vecMul, zero_dotProduct]
  have e2 : (replicateCol (Fin 1) (fun i => p.pr (ratV (vecB B.o B.ζ) i)) *ᵥ (y ∘ Sum.inr)) =
      y (Sum.inr 0) • (⇑ι ∘ vecB B.o B.ζ) := by
    funext i
    simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm, ratV, hι]
  rw [e1, zero_add, e2, smul_dotProduct, smul_eq_mul, mul_comm]
  congr 1
  change (⇑ι ∘ vecB B.o B.ζ) ⬝ᵥ (⇑ι ∘ r) = ι _
  rw [← RingHom.map_dotProduct, dotProduct_comm, h2]

end GlobalTheory.FinPl.GluedInt

open GlobalTheory.FinPl.GluedInt in

theorem GlobalTheory.FinPl.glued_last_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ _ hyp x hx
  have hu := hg.unit.2 B.V₀ L₀
  have hz := cAe_smul p (ratV (vecB B.o B.ζ))
  set zk : Fin B.V₀.rank → k := fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j)) with hzk
  have hN : ∀ y : n ⊕ Fin 1 → k, form p B.V₀ (β₀.b *ᵥ y) zk =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := form_frame p B β β₀ hg.sum
  have hvN := hg.norm
  set N := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) with hNdef
  have hq0 : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact q.ne_zero
  have hmem : (fun i => cA D (p.sec (zk i))) ∈ latV B.V₀ L₀ (· = p.v) := by
    rw [FrameLat.csec_mem_iff hsd]
    intro x' hx'
    have hb : β₀.b *ᵥ (β₀.b' *ᵥ x') = x' := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    have hy : β₀.b' *ᵥ x' ∈ gluedS q 1 P.ker P.vec := (hg.lat _).2 (by rw [hb]; exact hx')
    rw [← gluedLat_one, mem_gluedLat] at hy
    obtain ⟨s, -, hs⟩ := hy
    have h0 := (hs 0).2.1 rfl
    change form p B.V₀ x' zk ∈ 𝒪[k]
    rw [← hb, hN, h0, Valuation.mem_integer_iff, map_mul, map_mul, hvN, Unif.inv, map_inv₀, ← mul_assoc,
      mul_inv_cancel₀ hq0, one_mul]
    exact s.2
  have hA : cA D p.e • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by rw [hu, hz]; exact hmem
  have h1 := hyp (cA D p.e) hA
  rw [hu, hz, FrameLat.mt_csec] at h1
  rw [mt_sec' p] at hx
  have h2 := (FrameLat.csec_mem_iff hsd _).1 h1 _ hx
  rw [FrameLat.pairing_inv] at h2
  change form p B.V₀ (β₀.b *ᵥ x) zk ∈ 𝒪[k] at h2
  rw [hN, Valuation.mem_integer_iff, map_mul, hvN] at h2
  rw [Valuation.mem_integer_iff, map_mul]
  exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarAdelicUpperUnitriangularEntryTranslateInvariStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_adelicUpperUnitriangular_entry_translate_invariant : ∀ (D : D7) (ρ : ℕ) (ν : Measure (UX D ρ)), ν.IsHaarMeasure → Measurable (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ∧ IsFiniteMeasureOnCompacts (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν) ∧ ∀ t : Mx D ρ ρ, (∀ i j, ¬ i < j → t i j = 0) → Measure.map (fun x => x + t) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν) = Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν := by
  first | exact @GlobalTheory.UnitTransl.haar_val_add_invariant | exact GlobalTheory.UnitTransl.haar_val_add_invariant | (intros; apply GlobalTheory.UnitTransl.haar_val_add_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupportedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported : ∀ (D : D7) (S : HSp D) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → ∀ Λ : AddSubgroup (Fin S.rank → AE D), IsSDAt S v Λ → IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) := by
  first | exact @GlobalTheory.IwaPlace.SdComap.isSDAt_comap | exact GlobalTheory.IwaPlace.SdComap.isSDAt_comap | (intros; apply GlobalTheory.IwaPlace.SdComap.isSDAt_comap <;> assumption)
end

