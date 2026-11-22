import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegral
section
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_span_fin_of_fg {L : Type} [Field L] (O : ValuationSubring L) (n : ℕ) (N : Submodule O (Fin n → L))
    (hN : N.FG) : ∃ c : Fin n → Fin n → L, N = Submodule.span O (Set.range c) := by
  classical
  have : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  have : Module.Flat O N :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let k := Module.finrank O N
  let B : Module.Basis (Fin k) O N := Module.finBasis O N
  have hli : LinearIndependent O (fun i => (B i : Fin n → L)) :=
    B.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hliL : LinearIndependent L (fun i => (B i : Fin n → L)) :=
    (LinearIndependent.iff_fractionRing O L).1 hli
  have hk : k ≤ n := by simpa using hliL.fintype_card_le_finrank
  refine ⟨fun j => if h : (j : ℕ) < k then (B ⟨j, h⟩ : Fin n → L) else 0, le_antisymm ?_ ?_⟩
  · have hsp : N = Submodule.span O (Set.range fun i => (B i : Fin n → L)) := by
      have h1 := congrArg (Submodule.map N.subtype) B.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
      exact h1.symm
    refine hsp.le.trans (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by simp⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : (j : ℕ) < k
    · simp [h]
    · simp [h]

theorem mem_span_cols_iff {L : Type} [Field L] (O : ValuationSubring L) {n : ℕ} {ι : Type} [Fintype ι]
    (M : Matrix (Fin n) ι L) (v : Fin n → L) :
    v ∈ Submodule.span O (Set.range fun j i => M i j) ↔ ∃ u : ι → L, (∀ i, u i ∈ O) ∧ v = M *ᵥ u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => c j, fun j => (c j).2, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun j => ⟨u j, hu j⟩, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_square_span_cols : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  intro L _ _ n ι _ _ M
  let O : ValuationSubring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  obtain ⟨c, hc⟩ := exists_span_fin_of_fg O n (Submodule.span O (Set.range fun j i => M i j))
    (Submodule.fg_span (Set.finite_range _))
  refine ⟨Matrix.of fun i j => c j i, fun v => ?_⟩
  have h1 := mem_span_cols_iff O M v
  have h2 := mem_span_cols_iff O (Matrix.of fun i j => c j i) v
  rw [hc] at h1
  exact h1.symm.trans h2

end GlobalTheory.Hk3.HoweG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongr
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_smul_smul (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (s t : L) (u v : Fin n → L) :
    Formalism.UG.hform σ J (s • u) (t • v) = σ s * t * Formalism.UG.hform σ J u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_single_int {n : ℕ} (V : Matrix (Fin n) (Fin n) L) (hV : ∀ i j, V i j ∈ Formalism.UG.intL L) (i : Fin n) :
    ∀ r, (V *ᵥ Pi.single i (1 : L)) r ∈ Formalism.UG.intL L := by
  intro r
  have : (V *ᵥ Pi.single i (1 : L)) r = V r i := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]; exact hV r i

theorem single_eq_smul {n : ℕ} (i : Fin n) (c : L) : (Pi.single i c : Fin n → L) = c • Pi.single i (1 : L) := by
  ext r; by_cases h : r = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_class_columns : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  intro L _ _ ϖ σ q hU n n' JT x y V a hV hiff hG i j
  have hϖv : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact le_of_lt (by decide)
  have hϖ : ϖ ∈ Formalism.UG.intL L := hϖv
  set k := max (a i) (a j) with hk
  set c : L := ϖ ^ k with hc
  have hcI : c ∈ Formalism.UG.intL L := (Formalism.UG.intL L).pow_mem hϖ _

  have hcond : ∀ l, a l ≤ k → ∀ r, (x *ᵥ (c • (V *ᵥ Pi.single l (1 : L)))) r ∈ Formalism.UG.intL L := by
    intro l hl
    have hI : ∀ t, (Pi.single l c : Fin n → L) t ∈ Formalism.UG.intL L := by
      intro t; by_cases h : t = l
      · subst h; simpa using hcI
      · simp [Pi.single_apply, h, (Formalism.UG.intL L).zero_mem]
    have := (hiff (Pi.single l c) hI).mpr (by
      intro t; by_cases h : t = l
      · subst h
        refine ⟨ϖ ^ (k - a t), (Formalism.UG.intL L).pow_mem hϖ _, ?_⟩
        simp [hc, ← pow_add, Nat.add_sub_cancel' hl]
      · simpa [Pi.single_apply, h] using dvdPow_zero ϖ (a t))
    rwa [single_eq_smul, mulVec_smul] at this
  have hD := hG _ _ (mulVec_single_int V hV i) (mulVec_single_int V hV j) c hcI
    (hcond i (le_max_left _ _)) (hcond j (le_max_right _ _))
  refine ⟨_, hD, ?_⟩
  rw [single_eq_smul i, single_eq_smul j, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
    hform_smul_smul, hform_smul_smul, map_pow, hU.2.2.1, hc, ← mul_sub, ← mul_assoc, ← pow_add, ← pow_add,
    min_add_max]

end GlobalTheory.Hk3.IntWitt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOpsIffHeckeLiftsAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.HeckeLiftsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

theorem exists_extend {K L M H ι : Type} [Field K] [Field L] [AddCommGroup M] [Module K M] [AddCommGroup H] [Module L H]
    [Fintype ι] {σ : K →+* L} (j : M →ₛₗ[σ] H) (b : Module.Basis ι K M) (hli : LinearIndependent L fun i => j (b i))
    (hsp : Submodule.span L (Set.range j) = ⊤) (T : Module.End K M) :
    ∃ T' : Module.End L H, ∀ f, T' (j f) = j (T f) := by
  have hj : ∀ f, j f = ∑ i, σ (b.repr f i) • j (b i) := fun f => by
    conv_lhs => rw [← b.sum_repr f]
    simp only [map_sum, map_smulₛₗ]
  have hsp' : ⊤ ≤ Submodule.span L (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    rw [hj]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli hsp').constr L fun i => j (T (b i)), fun f => ?_⟩
  have h1 : ∀ i, (Module.Basis.mk hli hsp').constr L (fun i => j (T (b i))) (j (b i)) = j (T (b i)) := fun i => by
    have := (Module.Basis.mk hli hsp').constr_basis L (fun i => j (T (b i))) i
    rwa [Module.Basis.mk_apply] at this
  rw [hj f]
  conv_rhs => rw [← b.sum_repr f]
  simp only [map_sum, map_smulₛₗ, h1, RingHom.id_apply]

theorem isDC_image {H G : Type} [Group H] [Group G] [DecidableEq G] (φ : H →* G) (N J₀ : Subgroup H) (J : Subgroup G)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hJN : ∀ g ∈ J₀, g ∈ N)
    {α : H} (hα : α ∈ N) {R : Finset H} (hR : ∀ a ∈ R, a ∈ N) (h : Bridge.IsDC J₀ α R) :
    Bridge.IsDC J (φ α) (R.image φ) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 a' ha'
    exact ⟨⟨φ k₁, (hJ _ (hJN _ k₁.2)).2 k₁.2⟩, ⟨φ k₂, (hJ _ (hJN _ k₂.2)).2 k₂.2⟩, by simp only [map_mul]⟩
  · rintro _ ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
    obtain ⟨g₁, n₁, rfl⟩ := hs k₁
    obtain ⟨g₂, n₂, rfl⟩ := hs k₂
    obtain ⟨a, ⟨ha, haJ⟩, hu⟩ := h.2 (g₁ * α * g₂) ⟨⟨g₁, (hJ _ n₁).1 h₁⟩, ⟨g₂, (hJ _ n₂).1 h₂⟩, rfl⟩
    have key : ∀ c ∈ R, (φ c)⁻¹ * (φ g₁ * φ α * φ g₂) ∈ J ↔ c⁻¹ * (g₁ * α * g₂) ∈ J₀ := fun c hc => by
      rw [← hJ _ (N.mul_mem (N.inv_mem (hR c hc)) (N.mul_mem (N.mul_mem n₁ hα) n₂))]
      simp only [map_mul, map_inv]
    refine ⟨φ a, ⟨Finset.mem_image_of_mem _ ha, (key a ha).2 haJ⟩, ?_⟩
    rintro _ ⟨hc, hcJ⟩
    obtain ⟨c, hc', rfl⟩ := Finset.mem_image.1 hc
    rw [hu c ⟨hc', (key c hc').1 hcJ⟩]

theorem transport_local {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ : Subgroup H) (J : Subgroup G)
    (q : H → Prop) (χ : J → ℂ) (χ₀ : H → ℂ)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hJN : ∀ g ∈ J₀, g ∈ N) (hLN : ∀ g ∈ L₀, g ∈ N)
    (hc : ∀ g g', g ∈ L₀ → q g' → Commute g g') (hχe : ∀ g (h : φ g ∈ J), χ ⟨φ g, h⟩ = χ₀ g)
    (hχ : ∀ g ∈ J₀, g ∈ L₀ → χ₀ g = 1)
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, k₁ ∈ L₀ ∧ q k₂ ∧ k = k₁ * k₂)
    (hR : ∀ α ∈ L₀, ∃ R : Finset H, (∀ γ ∈ R, γ ∈ L₀) ∧ (∀ γ ∈ R, ∃ k₁ ∈ J₀ ⊓ L₀, ∃ k₂ ∈ J₀ ⊓ L₀, γ = k₁ * α * k₂) ∧
      ∀ y, (∃ k₁ ∈ J₀ ⊓ L₀, ∃ k₂ ∈ J₀ ⊓ L₀, y = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * y ∈ J₀ ⊓ L₀) :
    HkB.LocSplit J (L₀.map φ) ∧ (∀ k : J, (k : G) ∈ L₀.map φ → χ k = 1) ∧
      ∀ x ∈ L₀.map φ, ∃ B : Finset G, (∀ a ∈ B, a ∈ L₀.map φ) ∧ Bridge.IsDC J x B := by
  classical
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hs k
    obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp g ((hJ g hg).1 hk)
    refine ⟨φ k₁, (hJ _ (hJN _ h₁)).2 h₁, φ k₂, (hJ _ (hJN _ h₂)).2 h₂, ⟨k₁, s₁, rfl⟩, map_mul _ _ _, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact (hc l k₂ hl s₂).symm.map φ
  · rintro ⟨k, hk⟩ ⟨g, hg, hgk⟩
    obtain rfl : φ g = k := hgk
    rw [hχe, hχ g ((hJ g (hLN g hg)).1 hk) hg]
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨Rr, r0, r1, r2⟩ := hR α hα
    have hdc : Bridge.IsDC J₀ α Rr := by
      refine HeckeParts.isDC_of_local hα r0 (fun k hk => ?_) r1 r2
      obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp k hk
      exact ⟨k₁, h₁, k₂, h₂, s₁, hc α k₂ hα s₂, rfl⟩
    refine ⟨Rr.image φ, fun a ha => ?_, isDC_image φ N J₀ J hs hJ hJN (hLN α hα) (fun a ha => hLN a (r0 a ha)) hdc⟩
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    exact ⟨a', r0 a' ha', rfl⟩

end General

variable {D : D7}

theorem isInertPl_iff (P : Pl D.host.E) : IndefiniteRowSideFullHecke.InertSphericalIndices.IsInertPl P ↔ IsConjPl P P := by
  unfold IndefiniteRowSideFullHecke.InertSphericalIndices.IsInertPl
  rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · intro h
    have := SplitHeckeAdj.isConjPl_conj P
    rwa [HeightOneSpectrum.ext h] at this
  · intro h
    rw [← SplitHeckeAdj.eq_conj_of_isConjPl h]

theorem exists_idem {P : Pl D.host.E} (hP : IsConjPl P P) :
    ∃ e : Formalism.L2.Theta.AE D, IsPrimeIdem P e e ∧ (∀ f, Formalism.L2.JoinChr.IsPlIdem D f P ↔ f = e) ∧
      ∀ f, (∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧ f = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) ↔ f = e := by
  obtain ⟨Φ, hΦ⟩ := IdemSupport.exists_comp D
  obtain ⟨ε, hε⟩ := IdemSupport.exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := IdemSupport.place_comp hΦ hε
  have hc : P = IdemSupport.cP P := (IdemSupport.isConjPl_iff P P).1 hP
  have hd : IdemSupport.IsDelta Φ P (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (IdemSupport.eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  have hi := IdemSupport.place_idem hΦ hε
  have ht := (IdemSupport.tie_iff hΦ hi h0 P).2 hd
  refine ⟨_, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ht⟩, fun f => ⟨fun hf => ?_, ?_⟩, fun f => ⟨?_, ?_⟩⟩
  · obtain ⟨k1, ⟨v, ε', hε', k2⟩, kt⟩ := hf
    refine IdemSupport.delta_unique hΦ ((IdemSupport.tie_iff hΦ k1 ?_ P).1 kt) hd
    rcases k2 with ⟨k2, k3⟩ | k2
    · have : f = (f + cA D f) * f := by linear_combination -k1 - k2
      rw [this, k3, RingHom.map_mul, (IdemSupport.place_comp hΦ hε').1, zero_mul]
    · rw [k2, (IdemSupport.place_comp hΦ hε').1]
  · rintro rfl
    exact ⟨hi, ⟨_, ε, hε, Or.inr rfl⟩, ht⟩
  · rintro ⟨ε', hε', rfl⟩
    rw [IdemSupport.placeIdem_unique hε' hε]
  · rintro rfl
    exact ⟨ε, hε, rfl⟩

theorem isLocF_iff (V : HSp D) {P : Pl D.host.E} (hP : IsConjPl P P) (x : Bridge.Gf V) :
    IndefiniteRowSideFullHecke.InertSphericalIndices.IsLocF V P x ↔ IndefiniteRowSideFullHecke.LocalHeckeLifts.IsLocAt V P x := by
  obtain ⟨e, -, h1, h2⟩ := exists_idem hP
  constructor
  · rintro ⟨α, ⟨hα, ε, hε, hs⟩, hx⟩
    exact ⟨_, α, (h1 _).2 ((h2 _).1 ⟨ε, hε, rfl⟩), hα, hs, hx⟩
  · rintro ⟨f, α, hf, hα, hs, hx⟩
    obtain ⟨ε, hε, rfl⟩ := (h2 f).2 ((h1 f).1 hf)
    exact ⟨α, ⟨hα, ε, hε, hs⟩, hx⟩

set_option maxHeartbeats 800000 in

theorem exists_local (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1) {P : Pl D.host.E} (hP : IsConjPl P P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ IsConjPl PP PP) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ x, x ∈ Lc ↔ IndefiniteRowSideFullHecke.LocalHeckeLifts.IsLocAt V P x) ∧ HkB.LocSplit (levEnv V β L).J Lc ∧
      (∀ k : (levEnv V β L).J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L).χ k = 1) ∧
      ∀ x ∈ Lc, ∃ B : Finset (Bridge.Gf V), (∀ a ∈ B, a ∈ Lc) ∧ Bridge.IsDC (levEnv V β L).J x B := by
  classical
  obtain ⟨e, he, h1, -⟩ := exists_idem hP
  obtain ⟨hff, hcf, hG, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e he
  have hone : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff' : ∀ PP, PP ∈ (flag1L L).Pg ∨ PP ∈ (flag1L L).Q → PP ≠ P ∧ ¬ IsConjPl PP P := fun PP h => by
    refine ⟨fun e => hoff PP h (e ▸ hP), fun hc => hoff PP h ?_⟩
    have e1 := SplitHeckeAdj.eq_conj_of_isConjPl hc
    have e2 := SplitHeckeAdj.eq_conj_of_isConjPl hP
    have e3 : PP = P := by rw [e2, e1, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    exact e3 ▸ hP
  obtain ⟨-, hχ, hsp⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e e he hone hoff'
  have h5 := transport_local (SplitHeckeAdj.fin V) (GfC V) (levG V β (flag1L L)) (IdemSupport.suppGroup V e) (levEnv V β L).J
    (SuppF V (1 - e)) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L)) (SplitHeckeAdj.fin_lift V)
    (fun g => SplitHeckeAdj.mem_J V β L) (fun g hg => hg.1) hG (fun g g' => SplitHeckeAdj.commute_compl V e hff hcf)
    (fun g => SplitHeckeAdj.chi_eq V β L) hχ hsp fun α hα => by
      have h6 := HeckeLabels.exists_isCosetRep V β (flag1L L) he hα
      exact h6.imp fun Rr h => ⟨h.1, fun γ hγ => (h.2.1 γ hγ).2, h.2.2⟩
  refine ⟨(IdemSupport.suppGroup V e).map (SplitHeckeAdj.fin V), fun x => ⟨fun hx => ?_, fun hx => ?_⟩, h5.1,
    fun k hk => Units.ext (h5.2.1 k hk), h5.2.2⟩
  · exact hx.elim fun g hg => ⟨e, g, (h1 e).2 rfl, hG g hg.1, hg.1, (congrArg Subtype.val hg.2).symm⟩
  · exact hx.elim fun f hf => hf.elim fun g hg => ⟨g, (h1 f).1 hg.1 ▸ hg.2.2.1, Subtype.ext hg.2.2.2.symm⟩

section At

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem level_split (hC : R.Char F) (t : T) (PP : Pl D.host.E) (h : PP ∈ R.Pg ∨ PP ∈ R.Q t) : ¬ IsConjPl PP PP :=
  h.elim (fun h => TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg PP h PP h) fun h => (hC.lev.Q_pl t PP h).2 PP h

def forget (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : IndefiniteRowSideFullHecke.LocalHeckeLifts.SphOp R j t → IndefiniteRowSideFullHecke.InertSphericalIndices.SphIx A j t :=
  Sum.map id fun a => ⟨(a.1.1, a.1.2.1), (isInertPl_iff _).2 a.2.1, (isLocF_iff _ a.2.1 _).2 a.2.2.2.2.1⟩

open Classical in

def dropInert (R : RealDat D A Ks) : RealDat D A Ks := { R with Sb := R.Sb.filter fun P => ¬ IsConjPl P P }

end At

end GlobalTheory.HeckeLiftsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLattice
section
open Matrix

namespace GlobalTheory.Hk3.HoweG.GramA

variable {L : Type} [Field L]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (a b : Fin n → L) :
    Formalism.UG.hform σ J a b = (fun i => σ (a i)) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem map_mulVec_eq (σ : L →+* L) {n m : ℕ} (A : Matrix (Fin n) (Fin m) L) (w : Fin m → L) :
    (fun i => σ ((A *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT σ A := by
  ext i
  simp [Formalism.UG.cT, dotProduct, Matrix.mulVec, Matrix.vecMul, map_sum, mul_comm]

theorem dot_mem (O : Subring L) {n : ℕ} {a b : Fin n → L} (ha : ∀ i, a i ∈ O) (hb : ∀ i, b i ∈ O) : a ⬝ᵥ b ∈ O :=
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha k) (hb k)

theorem mulVec_mem (O : Subring L) {n m : ℕ} {A : Matrix (Fin n) (Fin m) L} {b : Fin m → L}
    (hA : ∀ i j, A i j ∈ O) (hb : ∀ i, b i ∈ O) : ∀ i, (A *ᵥ b) i ∈ O :=
  fun i => dot_mem O (hA i) hb

theorem hform_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  have hS' := HoweSwap.cT_herm hS
  have hT' := HoweSwap.cT_herm hT
  have hSi := HoweSwap.cT_inv_herm JS hS'
  have iS : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJS).1
  have iT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJT).1
  have hσO : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rw [hv]; exact hz
  have e1 : (JS : Matrix (Fin n) (Fin n) L) * adj σ JS JT x = Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj
    rw [Matrix.mul_assoc, HoweSwap.mul_inv_cl]
  have e2 : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    unfold adj
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hT', hSi, HoweSwap.cT_cT hσ, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  have e3 : x * adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
      (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj Formalism.UG.cT
    simp only [Matrix.mul_assoc]
  have h1 : ∀ b : Fin n → L, Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + adj σ JS JT x *ᵥ w) b =
      (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ b) +
        (fun i => σ (w i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ (x *ᵥ b)) := by
    intro b
    have : (fun i => σ ((u + adj σ JS JT x *ᵥ w) i)) = (fun i => σ (u i)) + fun i => σ ((adj σ JS JT x *ᵥ w) i) := by
      ext i; simp
    rw [hform_eq_dot, this, add_dotProduct, map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2,
      Matrix.mulVec_mulVec]
  have h2 : (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ (adj σ JS JT x *ᵥ w')) =
      (fun i => σ ((x *ᵥ u) i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]
  have h3 : x *ᵥ (adj σ JS JT x *ᵥ w') =
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *ᵥ
        ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e3]
  rw [h1, Matrix.mulVec_add, dotProduct_add, h2, Matrix.mulVec_add, h3]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact dot_mem _ (fun i => hσO _ (hu i)) (mulVec_mem _ iS hu')
  · exact dot_mem _ (fun i => hσO _ (hxu i)) (mulVec_mem _ iT hw')
  · refine dot_mem _ (fun i => hσO _ (hw i)) (mulVec_mem _ iT fun i => ?_)
    exact add_mem (hxu' i) (mulVec_mem _ hx (mulVec_mem _ iT hw') i)

end GlobalTheory.Hk3.HoweG.GramA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScaleStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  first | exact @GlobalTheory.HTW.RecS.jointB_of_large | exact GlobalTheory.HTW.RecS.jointB_of_large | (intros; apply GlobalTheory.HTW.RecS.jointB_of_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScaleStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrimeWordConditions_of_large_scale : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  first | exact @GlobalTheory.HTW.RecS.jointCD_of_large | exact GlobalTheory.HTW.RecS.jointCD_of_large | (intros; apply GlobalTheory.HTW.RecS.jointCD_of_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointConditionsRangeBoundStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_conditions_range_bound : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), AdmissibleParameterJ.JumpBoundClosedForm D → AdmissibleParameterJ.AdmJ large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i)) := by
  first | exact @GlobalTheory.closingFamilyX | exact GlobalTheory.closingFamilyX | (intros; apply GlobalTheory.closingFamilyX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTieEntire
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerTieEntire

theorem kerTie_entire : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ, ∀ i < D.R.m, ∀ c c', Differentiable ℂ ((t.O u μ).Th i c c') := by
  intro D L hT Gi Gl K Y cX ex t u μ i _ c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hAdm
  rw [t.O_Th u μ i c c']
  have hF := GlobalTheory.KerFinEntire.kerFin_entire D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok t.χ_ok _ _
    ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c') hAdm (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c')
  let T : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) →L[ℂ] VCx t.X.Tau (D.R.N i) (D.R.N (i + 1)) :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (t.seam.iT τ)
  exact hF.comp T.differentiable

end GlobalTheory.KerTieEntire
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelBasis_determinant_abs_at_place : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  first | exact @GlobalTheory.SatakeUnitDeterminantBasis.detB | exact GlobalTheory.SatakeUnitDeterminantBasis.detB | (intros; apply GlobalTheory.SatakeUnitDeterminantBasis.detB <;> assumption)
end

