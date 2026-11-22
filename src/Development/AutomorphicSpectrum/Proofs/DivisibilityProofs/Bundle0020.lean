import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AlgebraicIndependentLinearForms
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinKer

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem algebraicIndependent_linearForms {F E : Type} [Field F] [Field E] [Algebra F E]
    {D κ : Type} [Fintype D] [Fintype κ] (u : D → E) (hu : AlgebraicIndependent F u)
    (v : κ → D → F) (hv : LinearIndependent F v) :
    AlgebraicIndependent F fun i => ∑ c, algebraMap F E (v i c) * u c := by
  classical
  obtain ⟨T, hT⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F v)
    (LinearMap.ker_eq_bot.2 hv.fintypeLinearCombination_injective)
  have hTv : ∀ i, T (v i) = Pi.single i 1 := by
    intro i
    have := LinearMap.congr_fun hT (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hdual : ∀ i j, ∑ c, v i c * T (Pi.single c 1) j = (Pi.single i 1 : κ → F) j := by
    intro i j
    have hvi : v i = ∑ c, v i c • (Pi.single c 1 : D → F) := by
      ext d
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← hTv i]
    conv_rhs => rw [hvi]
    simp [map_sum, Finset.sum_apply]
  let A : MvPolynomial κ F →ₐ[F] MvPolynomial D F :=
    aeval fun i => ∑ c, MvPolynomial.C (v i c) * MvPolynomial.X c
  let B : MvPolynomial D F →ₐ[F] MvPolynomial κ F :=
    aeval fun c => ∑ j, MvPolynomial.C (T (Pi.single c 1) j) * MvPolynomial.X j
  have hBA : B.comp A = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [A, B, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply,
      algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum, hdual]
    simp [Pi.single_apply, ite_mul]
  have hA : Function.Injective A := by
    intro f g h
    have := congrArg B h
    have e : ∀ f, B (A f) = f := fun f => by
      simpa using DFunLike.congr_fun hBA f
    rwa [e, e] at this
  have hcomp : (aeval fun i => ∑ c, algebraMap F E (v i c) * u c : MvPolynomial κ F →ₐ[F] E) =
      (aeval u).comp A := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [A, map_sum, aeval_X, algHom_C]
  have : Function.Injective (aeval fun i => ∑ c, algebraMap F E (v i c) * u c :
      MvPolynomial κ F →ₐ[F] E) := by
    rw [hcomp]
    exact Function.Injective.comp (f := A) hu hA
  exact this

theorem ker_eq_span_homogeneous {F E : Type} [Field F] [Field E] [Algebra F E]
    {P D : Type} [Fintype P] [Fintype D] (u : D → E) (hu : AlgebraicIndependent F u)
    (l : P → D → F) :
    RingHom.ker (aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) : MvPolynomial P F →ₐ[F] E) =
      Ideal.span {f : MvPolynomial P F | f.IsHomogeneous 1 ∧
        aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) f = 0} := by
  classical
  set x : P → E := fun p => ∑ c, algebraMap F E (l p c) * u c with hx
  set S : Set (MvPolynomial P F) := {f | f.IsHomogeneous 1 ∧ aeval x f = 0} with hS
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F l
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hc : ∀ p, ∃ c : κ → F, ∑ i, c i • l (a i) = l p := by
    intro p
    have hp : l p ∈ Submodule.span F (Set.range (l ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, rfl⟩
    simpa using (Submodule.mem_span_range_iff_exists_fun F).1 hp
  choose c hc using hc
  let ρ' : MvPolynomial P F →ₐ[F] MvPolynomial κ F :=
    aeval fun p => ∑ i, MvPolynomial.C (c p i) * MvPolynomial.X i
  let ρ : MvPolynomial P F →ₐ[F] MvPolynomial P F := (rename a).comp ρ'
  have hρX : ∀ p, ρ (MvPolynomial.X p) = ∑ i, MvPolynomial.C (c p i) * MvPolynomial.X (a i) := by
    intro p
    simp [ρ, ρ', map_sum, aeval_X, rename_C, rename_X]
  have hxp : ∀ p, x p = ∑ i, algebraMap F E (c p i) * x (a i) := by
    intro p
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have : l p d = ∑ i, c p i * l (a i) d := by
      rw [← hc p]
      simp [Finset.sum_apply]
    rw [this, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
  have hmem : ∀ p, MvPolynomial.X p - ρ (MvPolynomial.X p) ∈ S := by
    intro p
    refine ⟨?_, ?_⟩
    · rw [hρX]
      exact (isHomogeneous_X F p).sub
        (IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (c p i) (a i))
    · rw [hρX]
      simp only [map_sub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq]
      simpa [sub_eq_zero] using hxp p
  have hle : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial P F →ₐ[F] E) := by
    rw [Ideal.span_le]
    intro f hf
    exact hf.2
  have hq : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp ρ = Ideal.Quotient.mkₐ F (Ideal.span S) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.Quotient.eq.2 (Ideal.subset_span (hmem p))).symm
  have hdiff : ∀ f, f - ρ f ∈ Ideal.span S := by
    intro f
    have := DFunLike.congr_fun hq f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq.1 this.symm
  refine le_antisymm ?_ hle
  intro f hf
  have hf0 : aeval x f = 0 := hf
  have h1 : aeval x (ρ f) = 0 := by
    have := hle (hdiff f)
    have h2 : aeval x (f - ρ f) = 0 := this
    rw [map_sub, hf0, zero_sub, neg_eq_zero] at h2
    exact h2
  have hind : AlgebraicIndependent F (x ∘ a) :=
    algebraicIndependent_linearForms u hu (l ∘ a) hli
  have h2 : ρ' f = 0 := by
    apply hind
    rw [map_zero, ← h1]
    simp [ρ, aeval_rename]
  have h3 : ρ f = 0 := by simp [ρ, h2]
  simpa [h3] using hdiff f

theorem ker_linearForms_span : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K), (∀ a : K, a = k₀) → ∀ (C : Type) [Fintype C]
    (u : C → E) (l : (Σ k, ι k) → C → F), AlgebraicIndependent F u →
    ∃ S : Set (MRingOver F ι), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧
      RingHom.ker (aeval (fun p => ∑ c, algebraMap F E (l p c) * u c) : MRingOver F ι →ₐ[F] E) =
        Ideal.span S := by
  intro F E _ _ _ K _ ι _ k₀ hk C _ u l hu
  refine ⟨_, ?_, ker_eq_span_homogeneous u hu l⟩
  rintro f ⟨hf, -⟩ m hm k
  have hd : ∑ p : (Σ k, ι k), m p = 1 := by
    have h : Finsupp.degree m = 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hf (mem_support_iff.1 hm)
    rw [← h, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun p _ hp => by simpa using hp).symm
  rw [Fintype.sum_sigma] at hd
  have hk' : ∀ j : K, j = k := fun j => (hk j).trans (hk k).symm
  rw [Fintype.sum_eq_single k (fun j hj => absurd (hk' j) hj)] at hd
  exact hd

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinKer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinearSubst
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear_subst : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime V → ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → genNum F V (fun t => ∑ i, M t i • cls i) H Q = genNum F V cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  exact @BaseChangeColon.genNum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeTieGalois
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def relabGroup (H : Host E) : Subgroup (Equiv.Perm (CMType H)) where
  carrier := {s | ∃ g : HostAut H, ∀ τ, (s τ).1 = τ.1.comp g.σ.toRingHom}
  one_mem' := ⟨HostAut.refl H, fun τ => by ext x; rfl⟩
  mul_mem' := by
    rintro s₁ s₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨⟨g₁.σ.trans g₂.σ, by simp [g₁.fix, g₂.fix]⟩, fun τ => ?_⟩
    rw [Equiv.Perm.mul_apply, h₁, h₂]
    ext x; rfl
  inv_mem' := by
    rintro s ⟨g, h⟩
    refine ⟨g.symm, fun τ => ?_⟩
    have e := h (s⁻¹ τ)
    rw [show s (s⁻¹ τ) = τ from Equiv.apply_symm_apply s τ] at e
    rw [e]
    ext x
    show _ = (s⁻¹ τ).1 (g.σ (g.σ.symm x))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA

open GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA in
theorem GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (S : ℕ → Finset ℕ) (n : ℕ) (tie : ∀ B k, HodgeTie Y (S B) n (T.M B k)), IsGalois ℚ E → Mono (spMap β) → T.Conv II → (∀ B k k', ∀ p ∈ S B, (tie B k').A.R p = (tie B k).A.R p) → (∀ (B : ℕ) (Φ : Xo.X ≅ Xo.X), Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm T.Comp, ∀ k, IsImageCpt Φ (tie B k).A (tie B (π k)).A) → T.PropA II := by
  intro hCmp hTw II hII E _ _ _ H D l Xo c O _ β Y _ T S n tie hGal hMono hConv hR hPerm
  refine GlobalTheory.T.tower_symmetry_limit_compat (CMType H) (D.p + D.q) T II (relabGroup H) hConv ?_ ?_ hII.1
  · intro τ τ'
    obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_host_aut_embedding E H τ.1 τ'.1 τ.2 τ'.2
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.cm_type_host_aut_permutation E H l c g
    exact ⟨π, ⟨g, hπ⟩, Subtype.ext ((hπ τ).trans hg.symm)⟩
  · intro s hs B _
    obtain ⟨g₀, hg₀⟩ := hs
    have hinv : ∀ τ, (s⁻¹ τ).1 = τ.1.comp g₀.symm.σ.toRingHom := by
      intro τ
      have e := hg₀ (s⁻¹ τ)
      rw [show s (s⁻¹ τ) = τ from Equiv.apply_symm_apply s τ] at e
      rw [e]
      ext x
      show _ = (s⁻¹ τ).1 (g₀.σ (g₀.σ.symm x))
      rw [RingEquiv.apply_symm_apply]
    obtain ⟨⟨a⟩, hA⟩ := hTw E H D l Xo g₀.symm
    obtain ⟨h, Φ, hΦ, ⟨m⟩⟩ := hA a
    obtain ⟨πc, himg⟩ := hPerm B Φ hΦ
    refine ⟨πc, fun k w => ?_⟩
    have key := hCmp II hII E H D l Xo c O β Y g₀.symm Φ m.toSABMap s⁻¹ (S B) n (T.M B k) (T.M B (πc k))
      (tie B k) (tie B (πc k)) hMono hΦ hinv (himg k) (fun p hp => hR B k (πc k) p hp)
      (fun j => (s (w j).1, (w j).2))
    have e2 : ∀ x, s⁻¹ (s x) = x := fun x => Equiv.symm_apply_apply s x
    simpa only [e2, Prod.mk.eta] using key
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsBlockMapDrop
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

theorem isBlockMap_drop (j : K → FlBlock Ψ N) (k₀ : K) :
    IsBlockMap (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
    have h' : (⟨a, x⟩ : Σ k, PIdx j k) = ⟨b, y⟩ := h
    cases h'
    rfl
  · rintro ⟨k, x⟩ ⟨⟨k', hk⟩, rfl⟩
    exact ⟨⟨⟨k', hk⟩, x⟩, rfl⟩

theorem imageZ_drop [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    imageZ (dropV j k₀) (PPart j) = PPart (dropJ j k₀) := by
  have key : ∀ f : MRing (PIdx (dropJ j k₀)), mConeMap (yPart j) (rename (dropV j k₀) f) =
      rename Subtype.val (mConeMap (yPart (dropJ j k₀)) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, yPart, dropV, dropJ]
  ext f
  simp only [imageZ, PPart, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  show mConeMap (yPart j) (rename (dropV j k₀) f) = 0 ↔ _
  rw [key]
  constructor
  · intro h
    exact rename_injective _ Subtype.val_injective (by rw [h, map_zero])
  · intro h
    have h' : mConeMap (yPart (dropJ j k₀)) f = 0 := h
    rw [h', map_zero]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumTermDiscreteValuation
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ), Q.IsHomogeneous (d + 1 - k) → (∀ i, (Hs i).IsHomogeneous (d - k)) → (k = d + 1 → ∀ i, Hs i = 0) → ∀ T : LocPair ι O (Ψ × Fin N), T.IsVert P ϖ → FlagChernComparison P d p j φ T → PowerSumsVanish P d (fun i : Fin N => T.x' (τ, i)) → T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p Ψ _ _ N j φ k hk1 hkd τ Q Hs hQ hHs hH0 T hT hM hPS
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.local_pair_value_linear O K ι (Ψ × Fin N) T P
  have hB : T.val P (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = 0 := by
    rcases Nat.lt_or_ge k (d + 1) with hlt | hge
    · exact GlobalTheory.T.vertical_pair_power_sum_vanish O ϖ hϖ K ι P d hP (Ψ × Fin N) T hT N (fun a => (τ, a)) hPS k (d - k) hk1
        (by omega) Hs hHs
    · have hk : k = d + 1 := by omega
      have h0 := hsmul 0 (fun _ => 0)
      simp only [mul_zero, zero_mul] at h0
      have hfun : (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) =
          (fun _ => (0 : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ)) := by
        funext i
        rw [hH0 hk i, mul_zero]
      rw [hfun]
      exact h0
  have hA : T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
        rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
          (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) =
      cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
    rw [GlobalTheory.T.local_pair_power_sum_value O K ι (Ψ × Fin N) T P N k (fun a => (τ, a)) (rename Sum.inl Q),
      support_rename_of_injective Sum.inl_injective,
      Finset.sum_image (Finsupp.mapDomain_injective Sum.inl_injective).injOn,
      GlobalTheory.T.cycle_number_mul_expand O K ι (Ψ × Fin N) (divCycle P (C (p : O))) T.x (bracket j φ p k τ) Q []]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hcl : classList (Sum.elim T.x T.x') (Finsupp.mapDomain Sum.inl μ) = classList T.x μ := by
      have hm : Finsupp.toMultiset (Finsupp.mapDomain (Sum.inl : Ψ × Fin N → (Ψ × Fin N) ⊕ (Ψ × Fin N)) μ) =
          (Finsupp.toMultiset μ).map Sum.inl := (Finsupp.toMultiset_map μ Sum.inl).symm
      unfold classList
      rw [hm, Multiset.map_map]
      rfl
    have hdeg : (classList T.x μ).length + k = d + 1 := by
      have h1 : (classList T.x μ).length = d + 1 - k := by
        have h2 := hQ (mem_support_iff.mp hμ)
        unfold classList
        rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
        rw [Finsupp.weight_apply] at h2
        exact (by simpa using h2 : (μ.sum fun _ c => c) = d + 1 - k)
      omega
    rw [coeff_rename_mapDomain _ Sum.inl_injective, hcl, List.append_nil, hM τ k hk1 _ hdeg]
  exact (hadd _ _).trans (by rw [hA, hB, add_zero])
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoCoeffGapDeltaOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem degree_prod_monic {σ ι : Type*} (m : MonomialOrder σ) (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (d : ι → σ →₀ ℕ)
    (h : ∀ i ∈ s, m.degree (P i) = d i ∧ m.leadingCoeff (P i) = 1) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, d i ∧ m.leadingCoeff (∏ i ∈ s, P i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [m.degree_one, m.leadingCoeff_one]
  | insert a s has ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ha1, ha2⟩ := h a (Finset.mem_insert_self a s)
    have hne : ∀ f : MvPolynomial σ ℝ, m.leadingCoeff f = 1 → f ≠ 0 := fun f hf =>
      m.leadingCoeff_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero)
    rw [Finset.prod_insert has, Finset.sum_insert has,
      m.degree_mul (hne _ ha2) (hne _ ih2), m.leadingCoeff_mul, ha1, ih1, ha2, ih2]
    simp

theorem lex_sum_Ico {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {n : ℕ} (v : Fin n → σ)
    (hv : StrictMono v) {a b : Fin n} (hab : a < b) :
    (MonomialOrder.lex : MonomialOrder σ).degree (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ))
        = Finsupp.single (v a) 1 ∧
      (MonomialOrder.lex : MonomialOrder σ).leadingCoeff
        (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ)) = 1 := by
  have hlt : ∀ s, a < s → (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v s) 1) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := fun s hs =>
    MonomialOrder.lex_lt_iff.mpr (Finsupp.Lex.single_strictAnti (hv hs))
  have hzero : (MonomialOrder.lex : MonomialOrder σ).toSyn 0 <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := by
    rw [map_zero, ← MonomialOrder.bot_eq_zero]
    refine bot_lt_iff_ne_bot.mpr fun h => ?_
    rw [MonomialOrder.bot_eq_zero] at h
    have h0 := (MonomialOrder.lex : MonomialOrder σ).toSyn.injective (h.trans (map_zero _).symm)
    simp at h0
  have hdegX : (MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)
      = Finsupp.single (v a) 1 := MonomialOrder.degree_X
  have hrest : (MonomialOrder.lex : MonomialOrder σ).toSyn
      ((MonomialOrder.lex : MonomialOrder σ).degree
        (∑ s ∈ Finset.Ioo a b, (X (v s) : MvPolynomial σ ℝ))) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn
        ((MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)) := by
    rw [hdegX, MonomialOrder.degree_lt_iff hzero]
    intro c hc
    obtain ⟨s, hs, hcs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hc)
    rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hcs
    rw [hcs]
    exact hlt s (Finset.mem_Ioo.mp hs).1
  rw [← Finset.Ioo_insert_left hab, Finset.sum_insert (by simp)]
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_add_of_lt hrest, hdegX]
  · rw [MonomialOrder.leadingCoeff_add_of_lt hrest, MonomialOrder.leadingCoeff_X]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem rhoM_eq_sum (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    (∑ τ : Ψ, ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1 : (Ψ × Fin N) →₀ ℕ)
      = rhoM Ψ N := by
  ext ⟨τ, a⟩
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_const, smul_eq_mul,
    Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single a]
  · simp [rhoM, Fin.card_Ioi]
  · intro b _ hb; simp [hb]
  · simp
  · intro τ' _ h; simp [h]
  · simp

theorem coeff_rhoM_gapDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    coeff (rhoM Ψ N) (gapDelta Ψ N) = 1 := by
  let e := Fintype.equivFin Ψ
  letI : LinearOrder (Ψ × Fin N) :=
    LinearOrder.lift' (fun p => toLex (e p.1, p.2)) (fun p q h => by
      have h' : (e p.1, p.2) = (e q.1, q.2) := toLex.injective h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h'
      exact Prod.ext (e.injective h1) h2)
  haveI : WellFoundedGT (Ψ × Fin N) := Finite.to_wellFoundedGT
  have hv : ∀ τ : Ψ, StrictMono (fun s : Fin N => (τ, s)) := fun τ s t hst => by
    show toLex (e τ, s) < toLex (e τ, t)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hst⟩)
  have key := CoeffDelta.degree_prod_monic (MonomialOrder.lex : MonomialOrder (Ψ × Fin N))
    Finset.univ
    (fun τ : Ψ => ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, (X (τ, s) : MvPolynomial _ ℝ))
    (fun τ => ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1)
    (fun τ _ => CoeffDelta.degree_prod_monic _ Finset.univ _ _ fun a _ =>
      CoeffDelta.degree_prod_monic _ _ _ _ fun b hb =>
        CoeffDelta.lex_sum_Ico (fun s => (τ, s)) (hv τ) (Finset.mem_Ioi.mp hb))
  have h2 := key.2
  rw [MonomialOrder.leadingCoeff, key.1, rhoM_eq_sum] at h2
  exact h2

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoFactorialProductEq
section
namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem prod_range_sub_eq_factorial (i n : ℕ) :
    ∏ k ∈ Finset.range n, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : i < n
    · obtain ⟨t, rfl⟩ : ∃ t, n = i + 1 + t := ⟨n - (i + 1), by omega⟩
      have e1 : i + 1 + t - 1 - i = t := by omega
      have e2 : i + 1 + t + 1 - 1 - i = t + 1 := by omega
      rw [if_pos h, e1, e2, Nat.factorial_succ]
      push_cast
      ring
    · have e1 : n - 1 - i = 0 := by omega
      have e2 : n + 1 - 1 - i = 0 := by omega
      rw [if_neg h, e1, e2]
      simp

theorem prod_rhoM_factorial (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∏ p, (((rhoM Ψ N) p).factorial : ℝ) =
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  have h := prod_range_sub_eq_factorial (i : ℕ) N
  rw [← Fin.prod_univ_eq_prod_range (fun k => if (i : ℕ) < k then ((k : ℝ) - ((i : ℕ) : ℝ)) else 1) N] at h
  have hr : (rhoM Ψ N) (τ, i) = N - 1 - (i : ℕ) := rfl
  rw [hr, ← h]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Fin.lt_def]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimitStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_comparison_limit : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | exact GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalDivisorGeometricNumberStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_divisor_geometric_number : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → ∀ (p : ℕ) [Fact p.Prime], (C (p : ℤ) : MRing ι ℤ) ∈ W → charOf W = p ∧ ¬ IsHorizontal W ∧ ∀ L : Fin D → K → ℤ, geoNum D W L = intNum (ZMod p) (extTo (ZMod p) W) L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum | exact GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum <;> assumption)
end

