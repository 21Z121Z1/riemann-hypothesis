import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnipotentSubgroupFiniteGeneration
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenExact

theorem mem_span_openFns_of_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ Q hQ hex θ hθ f hf hker
  let σ : Representation ℂ Q (IndSp (stdBlocks d hd) ρ) := (parInd (stdBlocks d hd) ρ).comp Q.subtype
  have hI : ∀ t : Q, ∀ v ∈ openFns d hd ρ, σ t v ∈ openFns d hd ρ := by
    intro t v hv g hg
    have h1 : v.1.1 (g * (t : GL (Fin N) k)) ≠ 0 := hg
    obtain ⟨p, hp, n, hn, e⟩ := hv _ h1
    show ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k (wOpen d hd) * n
    refine ⟨p, hp, n * (t : GL (Fin N) k)⁻¹, mul_mem hn (inv_mem (hQ t.2)), ?_⟩
    rw [← mul_assoc, ← e]
    group
  have hσs : IsSmooth σ := fun v => (isSmooth_parInd (stdBlocks d hd) ρ v).preimage continuous_subtype_val
  let ρ' : Representation ℂ Q (openFns d hd ρ) := GlobalTheory.PRep.sub σ (openFns d hd ρ) hI
  have hρs : IsSmooth ρ' := by
    intro v
    have : {t : Q | ρ' t v = v} = {t : Q | σ t (v : IndSp (stdBlocks d hd) ρ) = v} := by
      ext t
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hσs _
  let θ' : (⊤ : Subgroup Q) →* ℂˣ := θ.comp (⊤ : Subgroup Q).subtype
  have hopen : IsOpen (θ'.ker : Set (⊤ : Subgroup Q)) := by
    have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
      GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
    let j : (⊤ : Subgroup Q) → unipB k (Fin N) := fun x => ⟨x.1.1, hQ x.1.2⟩
    have hj : Continuous j :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    have hset : (θ'.ker : Set (⊤ : Subgroup Q)) = j ⁻¹' ((whitChar ψ N).ker : Set (unipB k (Fin N))) := by
      ext x
      show θ x.1 = 1 ↔ whitChar ψ N (j x) = 1
      rw [hθ x.1 (hQ x.1.2)]
    rw [hset]
    exact hw.preimage hj
  have hexh : ∀ s : Finset Q, (↑s : Set Q) ⊆ (⊤ : Subgroup Q) →
      ∃ L : Subgroup Q, L ≤ ⊤ ∧ (↑s : Set Q) ⊆ L ∧ IsCompact (L : Set Q) := by
    classical
    intro s _
    obtain ⟨L, hLQ, hsL, hLc⟩ := hex (s.image Subtype.val) (by
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2)
    refine ⟨L.subgroupOf Q, le_top, ?_, ?_⟩
    · intro x hx
      refine Subgroup.mem_subgroupOf.2 (hsL ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    · rw [Subtype.isCompact_iff]
      have himg : ((↑) : Q → GL (Fin N) k) '' (L.subgroupOf Q : Set Q) = (L : Set (GL (Fin N) k)) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.1 hy
        · intro hx
          exact ⟨⟨x, hLQ hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [himg]
      exact hLc
  have hle : twKer (parInd (stdBlocks d hd) ρ) Q θ ≤ twKer σ ⊤ θ' :=
    Submodule.span_le.2 (by
      rintro w ⟨q, v, rfl⟩
      exact Submodule.subset_span ⟨⟨q, trivial⟩, v, rfl⟩)
  have key : (⟨f, hf⟩ : openFns d hd ρ) ∈ twKer ρ' ⊤ θ' :=
    GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρ' σ hρs hσs ⊤ θ' hopen hexh (openFns d hd ρ).subtype
      (Submodule.injective_subtype _) (fun _ _ => rfl) ⟨f, hf⟩ (hle hker)
  have hle2 : twKer ρ' ⊤ θ' ≤ (Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ,
      x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g}).comap (openFns d hd ρ).subtype :=
    Submodule.span_le.2 (by
      rintro _ ⟨q, g, rfl⟩
      exact Submodule.subset_span ⟨q.1, g.1, g.2, rfl⟩)
  exact hle2 key

end GlobalTheory.CompanionTheory.Rodier.OpenExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBound
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {r : ℕ}

theorem cone_anti {c c' : ℝ} (hcc : c' ≤ c) {t : Fin r → ℝ} (ht : t ∈ cone r c) : t ∈ cone r c' :=
  ⟨ht.1, fun i j h => (mul_le_mul_of_nonneg_right hcc (ht.1 j).le).trans (ht.2.1 i j h),
    fun i h => hcc.trans (ht.2.2 i h)⟩

theorem cone_step {c : ℝ} (hc0 : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (d : ℕ) :
    ∀ a b : Fin r, b.val = a.val + d → c ^ d * t b ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have e : b = a := Fin.ext (by simpa using h)
    subst e
    simp
  | succ d ih =>
    intro a b h
    have hm : a.val + d < r := by
      have := b.2
      omega
    have h1 := ih a ⟨a.val + d, hm⟩ rfl
    have h2 := ht.2.1 ⟨a.val + d, hm⟩ b (by simp only []; omega)
    calc c ^ (d + 1) * t b = c ^ d * (c * t b) := by ring
      _ ≤ c ^ d * t ⟨a.val + d, hm⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ t a := h1

theorem cone_pow_mul_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    {a b : Fin r} (hab : a ≤ b) : c ^ r * t b ≤ t a := by
  have hab' : a.val ≤ b.val := hab
  have h1 := cone_step hc0 ht (b.val - a.val) a b (by omega)
  have hle : c ^ r ≤ c ^ (b.val - a.val) :=
    pow_le_pow_of_le_one hc0.le hc1 (by have := b.2; omega)
  exact (mul_le_mul_of_nonneg_right hle (ht.1 b).le).trans h1

theorem cone_pow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    (i : Fin r) : c ^ r ≤ t i := by
  have hi := i.2
  have hl : r - 1 < r := by omega
  have h1 := cone_step hc0 ht (r - 1 - i.val) i ⟨r - 1, hl⟩ (by simp only []; omega)
  have h2 := ht.2.2 ⟨r - 1, hl⟩ (by simp only []; omega)
  calc c ^ r ≤ c ^ (r - 1 - i.val + 1) := pow_le_pow_of_le_one hc0.le hc1 (by omega)
    _ = c ^ (r - 1 - i.val) * c := pow_succ _ _
    _ ≤ c ^ (r - 1 - i.val) * t ⟨r - 1, hl⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ t i := h1

theorem weights_across_levels {e A T wa wb : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (heA : e ≤ A) (heT : e ≤ T)
    (h : (e * A ≤ wa ∧ wb * e ^ 2 ≤ T) ∨ (e ^ 2 ≤ wa * T ∧ e * A * wb ≤ 1) ∨ (e * A ≤ wa ∧ e * A * wb ≤ 1)) :
    wb * (e ^ 4 * A) ≤ T * wa := by
  have hA0 : 0 < A := he0.trans_le heA
  have hT0 : 0 < T := he0.trans_le heT
  have hee : e * e ^ 2 ≤ e ^ 2 := by
    have : 0 ≤ e ^ 2 := by positivity
    nlinarith
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : e * (e * A) ≤ wa := by
      have : 0 ≤ e * A := by positivity
      nlinarith
    calc wb * (e ^ 4 * A) = (wb * e ^ 2) * (e * (e * A)) := by ring
      _ ≤ T * wa := mul_le_mul h2 h3 (by positivity) hT0.le
  · calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * e ^ 2 := mul_le_mul h2 hee (by positivity) zero_le_one
      _ = e ^ 2 := one_mul _
      _ ≤ wa * T := h1
      _ = T * wa := mul_comm _ _
  · have h3 : e * e ^ 2 ≤ T * wa := by
      calc e * e ^ 2 = e * (e * e) := by ring
        _ ≤ T * (e * A) := mul_le_mul heT (mul_le_mul_of_nonneg_left heA he0.le) (by positivity) hT0.le
        _ ≤ T * wa := mul_le_mul_of_nonneg_left h1 hT0.le
    calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * (e * e ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = e * e ^ 2 := one_mul _
      _ ≤ T * wa := h3

theorem frameWt_div_le_div_ratio : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c,
    ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  intro r c hc
  have hc0 : 0 < min c 1 := lt_min hc one_pos
  have hc1 : min c 1 ≤ 1 := min_le_right _ _
  set c' := min c 1 with hc'
  set e := c' ^ r with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := pow_le_one₀ hc0.le hc1
  refine ⟨(e ^ 4)⁻¹, by positivity, fun s t ht0 α β hlev => ?_⟩
  have ht : t ∈ cone r c' := cone_anti (min_le_left _ _) ht0
  have hpos := ht.1
  have hge : ∀ i, e ≤ t i := cone_pow_le hc0 hc1 ht
  have hle : ∀ {a b : Fin r}, a ≤ b → e * t b ≤ t a := fun h => cone_pow_mul_le hc0 hc1 ht h
  have hsq : e ^ 2 ≤ e := by nlinarith
  obtain ⟨T, heT, hrat, hTb⟩ : ∃ T, e ≤ T ∧ ratio t s = t s / T ∧ ∀ b : Fin r, s < b → e * t b ≤ T := by
    by_cases h : s.val + 1 < r
    · refine ⟨t ⟨s.val + 1, h⟩, hge _, by simp [ratio, h], fun b hb => hle ?_⟩
      have hb' : s.val < b.val := hb
      exact Fin.le_def.2 (by simp only []; omega)
    · refine ⟨1, he1, by simp [ratio, h], fun b hb => ?_⟩
      have hb' : s.val < b.val := hb
      have := b.2
      omega
  have hT0 : 0 < T := he0.trans_le heT
  have lev2 : ∀ γ, frameLev s γ = 2 → e * t s ≤ frameWt t γ := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simpa [frameWt] using hle ha
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
  have lev0 : ∀ γ, frameLev s γ = 0 → e * t s * frameWt t γ ≤ 1 := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simp only [frameWt]
      rw [← div_eq_mul_inv]
      exact (div_le_one (hpos a)).2 (hle ha)
  have lev1 : ∀ γ, frameLev s γ = 1 → e ^ 2 ≤ frameWt t γ * T ∧ frameWt t γ * e ^ 2 ≤ T := by
    intro γ h
    have key : ∀ b : Fin r, s < b → e ^ 2 ≤ t b * T ∧ t b * e ^ 2 ≤ T := fun b hb => by
      have h1 := hTb b hb
      have h2 := hge b
      constructor
      · rw [sq]
        exact mul_le_mul h2 heT he0.le (hpos b).le
      · have : 0 ≤ e * t b := (mul_pos he0 (hpos b)).le
        nlinarith
    rcases γ with _ | a | a
    · simp only [frameWt, one_mul]
      exact ⟨hsq.trans heT, hsq.trans heT⟩
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      simpa [frameWt] using key a ha
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      have h1 := hTb a ha
      have h2 := hge a
      simp only [frameWt]
      rw [inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀ (hpos a), div_le_iff₀ (hpos a)]
      constructor
      · have : 0 ≤ e * t a := (mul_pos he0 (hpos a)).le
        nlinarith
      · rw [sq]
        exact mul_le_mul heT h2 he0.le hT0.le |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have lvl : ∀ γ, frameLev s γ = 0 ∨ frameLev s γ = 1 ∨ frameLev s γ = 2 := by
    intro γ
    rcases γ with _ | a | a <;> simp only [frameLev] <;> (try split_ifs) <;> simp
  have hcases : (e * t s ≤ frameWt t α ∧ frameWt t β * e ^ 2 ≤ T) ∨
      (e ^ 2 ≤ frameWt t α * T ∧ e * t s * frameWt t β ≤ 1) ∨
      (e * t s ≤ frameWt t α ∧ e * t s * frameWt t β ≤ 1) := by
    rcases lvl α with a | a | a <;> rcases lvl β with b | b | b <;> rw [a, b] at hlev <;>
      first
        | exact Or.inl ⟨lev2 α a, (lev1 β b).2⟩
        | exact Or.inr (Or.inl ⟨(lev1 α a).1, lev0 β b⟩)
        | exact Or.inr (Or.inr ⟨lev2 α a, lev0 β b⟩)
        | (exfalso; omega)
  have key := weights_across_levels he0 he1 (hge s) heT hcases
  have hwa : 0 < frameWt t α := frameWt_pos hpos α
  have hA0 : 0 < t s := hpos s
  have hK : (e ^ 4)⁻¹ / ratio t s = T / (e ^ 4 * t s) := by
    rw [hrat]
    field_simp
  rw [hK, div_le_div_iff₀ hwa (by positivity)]
  exact key

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermVol

variable (D : D7) (r : ℕ)

def hermPart (x : Mx D r r) : Mx D r r := half D • (x + adj x)

variable {D r}

theorem hermPart_mem (x : Mx D r r) : hermPart D r x ∈ hermA D r := by
  change adj (hermPart D r x) = hermPart D r x
  rw [hermPart, adj_smul, cA_half, adj_add, adj_adj, add_comm]

theorem hermPart_of_mem {c : Mx D r r} (hc : c ∈ hermA D r) : hermPart D r c = c := by
  have h : adj c = c := hc
  rw [hermPart, h, smul_add, half_smul_add]

theorem hermPart_add (x y : Mx D r r) : hermPart D r (x + y) = hermPart D r x + hermPart D r y := by
  rw [hermPart, hermPart, hermPart, adj_add, add_add_add_comm, smul_add]

theorem hermPart_rat {x : Mx D r r} (hx : x ∈ ratMx D r r) : hermPart D r x ∈ ratMx D r r := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ + γᴴ), ?_⟩
  rw [rat_smul, rat_add, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_hermPart : Continuous (hermPart D r) :=
  haveI : IsTopologicalAddGroup (Mx D r r) := (lattice_Mx D r r).1
  show Continuous fun x => half D • (x + adj x) from (continuous_id.add continuous_adj).const_smul (half D)

theorem isClosed_hermA : IsClosed (hermA D r : Set (Mx D r r)) :=
  haveI : T2Space (Mx D r r) := (lattice_Mx D r r).2.2.2.1
  isClosed_eq continuous_adj continuous_id

theorem isCoLat_herm : GlobalTheory.CuspGeneric.IsCoLat (ratHerm D r) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D r r
  refine ⟨?_, ?_⟩
  · let φ : ratHerm D r → ratMx D r r := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D r r → hermA D r := fun x => ⟨hermPart D r x, hermPart_mem x⟩
    have hP : Continuous P := continuous_hermPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_comap.2 (hermPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change hermPart D r (γ + x.1) = hermPart D r γ + x.1
    rw [hermPart_add, hermPart_of_mem x.2]

theorem exists_isCovolOneH : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖 := by
  intro D r
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) := (isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (hermA D r) _ isCoLat_herm
  exact ⟨μ, 𝓕, hμ, hF, h1⟩

end GlobalTheory.CompanionTheory.HermVol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSInf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.JSInfStep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

variable [IsTotallyComplex E]

def chiInf (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHomClass.toAddMonoidHom (sInf E))

theorem chiInf_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chiInf ψ z = ψ (sInf E z) := rfl

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem chiInf_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E)
    (h : ∀ w, chiInf ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by
    have e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c)) := by
      refine ad_ext ?_ ?_
      · rw [map_mul, pInf_sInf, pInf_sInf]
      · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]
    rw [e]
    exact h _
  obtain ⟨w⟩ := nonempty_pl (E := E)
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0 := by
    change pFin E (algebraMap E (Ad E) d) = 0
    rw [← hd, pFin_sInf]
  have hd0 : d = 0 := (injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

end GlobalTheory.CompanionTheory.JSInfStep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.Growth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem exists_unip_bound {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : BlockIx a r → Ad E) (y : GL (Fin a) (Cinf E)),
      ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hT : IsCompact ((fun x => JointCont.finPart g x) '' Cm) :=
    hCm.image (JointCont.continuous_finPart g)
  obtain ⟨C₀, N, hC₀, hgrow⟩ := GlobalTheory.CompanionTheory.BoxBound.exists_growth_uniform hφ hT
  have hI : Continuous (fun x : BlockIx a r → Ad E => JointCont.infPart g x) := by
    have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
      continuous_pi fun p => JointCont.continuous_pInf.comp (continuous_apply p)
    exact (JointCont.continuous_unip.comp h1).mul continuous_const
  obtain ⟨B, hB⟩ := (hCm.image (GlobalTheory.CompanionTheory.BoxBound.continuous_height.comp hI)).bddAbove
  have hc : (0 : ℝ) ≤ 1 + 2 * a := by positivity
  refine ⟨C₀ * ((1 + 2 * a) * max B 1) ^ N, N, by positivity, fun x y => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Cm, x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  have e1 : unip ((fun p => algebraMap E (Ad E) (q p)) + x') * (g * infGL E a y) =
      ratGL E a (unip q) * (finGL E a (JointCont.finPart g x') * infGL E a (JointCont.infPart g x' * y)) := by
    rw [unip_add, unip_algebraMap, mul_assoc, ← mul_assoc (unip x'), JointCont.unip_mul_eq, map_mul, mul_assoc]
  rw [e1, hφ.left]
  refine (hgrow _ ⟨x', hx'm, rfl⟩ _).trans ?_
  have hb : height (JointCont.infPart g x') ≤ max B 1 := le_trans (hB ⟨x', hx'm, rfl⟩) (le_max_left _ _)
  have hy := one_le_height y
  have hH : height (JointCont.infPart g x' * y) ≤ (1 + 2 * a) * max B 1 * height y := by
    refine (GlobalTheory.CompanionTheory.BoxBound.height_mul_le' _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) hc
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [one_le_height (JointCont.infPart g x' * y)]) hH N) hC₀

theorem ct_growth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r φ hφ _ _ μ 𝓕 hμ hF g
  have := hμ
  obtain ⟨C, N, -, h⟩ := exists_unip_bound (r := r) hφ g
  refine ⟨C * μ.real 𝓕, N, fun y => ?_⟩
  refine (norm_setIntegral_le_of_norm_le_const (covol_lt_top μ 𝓕 hF) fun x _ => h x y).trans_eq ?_
  ring

end GlobalTheory.CompanionTheory.CTFin.Growth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConstantTermSmallStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_constant_term_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation | exact GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosedStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_generalized_space_span_closed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1}, φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms | exact GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms | (intros; apply GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIsoStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_twisted_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | exact GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw <;> assumption)
end

