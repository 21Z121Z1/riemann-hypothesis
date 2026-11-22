import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ErrorDataOfNormGenerators
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.SplitGen

theorem exists_places {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hc : p % (H.QS * H.q * H.d) = 1)
    (ι : Type) [Fintype ι] (hι : Fintype.card ι = R.f) :
    ∃ φ : ι → HeightOneSpectrum (𝓞 H.F), Function.Injective φ ∧ ∀ v, (p : 𝓞 H.F) ∈ (φ v).asIdeal := by
  have h1 := Formalism.MainNotions.Gaps.LevGap.split_F H p hp (GlobalTheory.HostSplit.split_of_one_mod R H p hp hc).1
  have hpos : 0 < Module.finrank ℚ H.F := Module.finrank_pos
  have hfin : {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [h1]; exact hpos)
  haveI := hfin.to_subtype
  have h2 : Nat.card ι = Nat.card {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal} := by
    rw [Nat.card_coe_set_eq, h1, Formalism.MainNotions.Gaps.LevGap.finrank_F, Nat.card_eq_fintype_card, hι]
  obtain ⟨e⟩ := Finite.card_eq.1 h2
  exact ⟨fun v => (e v).1, Subtype.val_injective.comp e.injective, fun v => (e v).2⟩

theorem nonempty_errX : ∀ X : Stages, (∀ i, ∃ π : 𝓞 X.B.host.E, (π : X.B.host.E) ∈ X.B.host.K ∧
    (π : X.B.host.E) * X.B.host.conj (π : X.B.host.E) = (X.B.host.g i : X.B.host.E)) → Nonempty (ErrX X.toD7) := by
  intro X h
  choose pG hG1 hG2 using h
  choose pT hT1 hT2 hT3 using X.toD7.T_norm
  have hv : ∀ u, ∃ φ : (X.toD7.mem u).A.vT → HeightOneSpectrum (𝓞 X.toD7.host.F), Function.Injective φ ∧
      ∀ v, ((X.toD7.mem u).A.T : 𝓞 X.toD7.host.F) ∈ (φ v).asIdeal := by
    intro u
    letI := (X.toD7.mem u).A.vTFin
    refine exists_places X.toD7.host (X.toD7.mem u).A.T_prime ?_ _ (X.toD7.mem u).A.card_vT
    have h1 : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [h1]
    exact X.B.T_cond u
  choose φ hφ1 hφ2 using hv
  exact ⟨⟨pG, hG1, hG2, pT, hT1, hT2, hT3, φ, hφ1, hφ2⟩⟩

end GlobalTheory.SplitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBaseOfRich
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.BaseExt

namespace GlobalTheory.FieldSize

def toComap (F K : IntermediateField ℚ ℂ) (h : F ≤ K) : F →+* (F.comap K.val : IntermediateField ℚ K) :=
  (IntermediateField.inclusion h : F →+* K).codRestrict (F.comap K.val) fun x => x.2

theorem image_toComap {E : Type} [Field E] (F K : IntermediateField ℚ ℂ) (h : F ≤ K) (𝔞 : Ideal (𝓞 E))
    (c : E → ℂ) (e : E → K) (he : ∀ a, (e a : ℂ) = c a) :
    extend (toComap F K h) (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = c (a : E)}) =
      Submodule.span (𝓞 (F.comap K.val : IntermediateField ℚ K))
        {x : (F.comap K.val : IntermediateField ℚ K) | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨⟨(x.1 : ℂ), x.2⟩, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem exists_base_of_rich : ∀ (P : Pre) (F : IntermediateField ℚ ℂ), FiniteDimensional ℚ F → Rich P F →
    ∀ S₁ S₂ : Finset ℂ, (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) →
    ∃ B : Base, B.toPre = P ∧ (∀ z, z ∈ F ↔ ∃ x ∈ B.Ks, B.embLL x = z) ∧
      (∀ z ∈ S₁, ∃ x ∈ B.LL0, B.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B.LL, B.embLL x = z := by
  classical
  intro B F hF hr S₁ S₂ h₁ h₂
  have : NumberField F := {}
  obtain ⟨SF, hSF, hE⟩ := exists_gens F
  let A : Finset ℕ := {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable
    (S₁ ∪ S₂ ∪ SF ∪ SR) (by
      intro z hz
      simp only [Finset.mem_union] at hz
      rcases hz with ((hz | hz) | hz) | hz
      exacts [h₁ z hz, h₂ z hz, hSF z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N])
  simp only [Finset.mem_union] at hS
  have hFK : F ≤ K := fun z hz => hE K (fun z hz => hS z (.inl (.inr hz))) F.val ⟨z, hz⟩
  have hEK : ∀ x, B.host.φ₀ x ∈ K := fun x => hFK (hr.host x)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (.inr hz)
  have : NumberField K := {}
  let f := toComap F K hFK
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K hEK
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := F.comap K.val
            Ks_le := le_top
            E_le_Ks := fun x => hr.host x
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (by simp [A])⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, ?_, ?_, ?_⟩
  · intro N hN
    have h := hr.roots N (List.mem_append_left [_, _, _, _, _] hN)
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro N hN
    have h := hr.roots N (List.mem_append_right [_, _, _, _, _] (List.mem_append_left [_, _] hN))
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hr.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_toComap F K hFK 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K hEK) fun _ => rfl)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hr.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_toComap F K hFK 𝔞 (fun a => B.host.φ₀ (B.host.sigmaOf g a))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_toComap F K hFK 𝔞 (fun a => B.host.φ₀ (B.host.sigmaOf g (B.host.conj a)))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g (B.host.conj a))) fun _ => rfl
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · intro z
    refine ⟨fun hz => ⟨⟨z, hFK hz⟩, hz, rfl⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact hx
  · exact fun z hz => ⟨⟨z, hS z (.inl (.inl (.inl hz)))⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (.inl (.inl (.inr hz)))⟩, rfl⟩

end GlobalTheory.FieldSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem exists_hostK : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (_ : IsTotallyComplex K), Module.finrank ℚ K = 2 ∧ discr K = -(H.d : ℤ) ∧ discr K < -4 ∧ K ≤ H.φ₀.toRatAlgHom.fieldRange ∧ (∀ z : ℂ, (∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + H.φ₀ H.sqrtMinusD) / 2)) ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) ∧ Module.finrank ℚ H.E = 2 * R.f := by
  intro R H
  obtain ⟨-, hd, -, hd16, -⟩ := H.hyp
  have hb : (H.φ₀ H.sqrtMinusD) ^ 2 = -(H.d : ℂ) := by
    have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
    rw [← map_pow, h, map_neg, map_natCast]
  let σ : H.K →ₐ[ℚ] ℂ := H.φ₀.toRatAlgHom.comp H.K.val
  let e : H.K ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  have hfd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  have hNF : NumberField σ.fieldRange := NumberField.mk
  have h2 : Module.finrank ℚ σ.fieldRange = 2 :=
    e.toLinearEquiv.finrank_eq.symm.trans
      (Formalism.FrobeniusOrbits.SplitK.finrank_K hd.pos (H.sqd_sq))
  let r : σ.fieldRange := ⟨H.φ₀ H.sqrtMinusD, ⟨Formalism.FrobeniusOrbits.SplitK.bK H.sqrtMinusD, rfl⟩⟩
  have hr : r ^ 2 = -(H.d : σ.fieldRange) := by
    apply Subtype.ext
    simpa [r] using hb
  have h4 : H.d % 4 = 3 := by omega
  have hD : discr σ.fieldRange = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 hd.squarefree h4 hr
  have hTC : IsTotallyComplex σ.fieldRange := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    let ψ := InfinitePlace.embedding_of_isReal hv
    have h1 : ψ r ^ 2 = -(H.d : ℝ) := by rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg (ψ r)]
  obtain ⟨x, -, hx, -, hgen, -⟩ := ringOfIntegers_sqrt_neg_three_mod_four H.d hd.squarefree h4 σ.fieldRange h2 r hr
  have hx' : ((x : σ.fieldRange) : ℂ) = (1 + H.φ₀ H.sqrtMinusD) / 2 := by
    have := congrArg (fun y : σ.fieldRange => (y : ℂ)) hx
    simp only [r] at this
    push_cast at this
    have e2 : ((2 : σ.fieldRange) : ℂ) = 2 := rfl
    rw [e2] at this
    linear_combination this / 2
  have hc : ∀ m n : ℤ, ((((m : 𝓞 σ.fieldRange) + n * x : 𝓞 σ.fieldRange) : σ.fieldRange) : ℂ) =
      m + n * ((1 + H.φ₀ H.sqrtMinusD) / 2) := fun m n => by
    rw [← hx']
    simp
  refine ⟨σ.fieldRange, hNF, hTC, h2, hD, by omega, ?_, fun z => ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(y : H.E), rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, hc s.1 s.2⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨m, n, rfl⟩ := hgen a
    exact ⟨(m, n), hc m n⟩
  · rw [H.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem exists_hom_of_ann {R V M : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R V] {d : ℕ} (w : Fin d → V) (m₀ : M) (h : ∀ α : R, α • w = 0 → α • m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[R] M), ∑ a, T a (w a) = m₀ ∧ ∀ a v, ∃ α : R, T a v = α • m₀ := by
  classical
  let f : R →ₗ[R] (Fin d → V) := LinearMap.toSpanSingleton R _ w
  let g : R →ₗ[R] M := LinearMap.toSpanSingleton R _ m₀
  have hk : LinearMap.ker f ≤ LinearMap.ker g := fun α hα => h α hα
  let φ : LinearMap.range f →ₗ[R] M := (LinearMap.ker f).liftQ g hk ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ α : R, φ ⟨f α, α, rfl⟩ = α • m₀ := by
    intro α
    have : f.quotKerEquivRange.symm ⟨f α, α, rfl⟩ = Submodule.Quotient.mk α := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker f).liftQ g hk (f.quotKerEquivRange.symm ⟨f α, α, rfl⟩) = _
    rw [this]; rfl
  obtain ⟨P, hP⟩ := IsSemisimpleModule.extension_property (LinearMap.range f).subtype
    (LinearMap.range f).injective_subtype LinearMap.id
  refine ⟨fun a => φ ∘ₗ P ∘ₗ LinearMap.single R (fun _ => V) a, ?_, fun a v => ?_⟩
  · have e : ∑ a, Pi.single a (w a) = (LinearMap.range f).subtype ⟨f 1, 1, rfl⟩ := by
      rw [Finset.univ_sum_single]
      exact (one_smul R w).symm
    have e2 := LinearMap.congr_fun hP ⟨f 1, 1, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_single]
    rw [← map_sum, ← map_sum, e]
    rw [LinearMap.comp_apply] at e2
    rw [e2, LinearMap.id_apply, hφ, one_smul]
  · obtain ⟨α, hα⟩ := (P (Pi.single a v)).2
    refine ⟨α, ?_⟩
    rw [← hφ]
    exact congrArg φ (Subtype.ext hα.symm)

theorem exists_words {L : Type} (α : FreeAlgebra ℂ L) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), α = ∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod := by
  have h1 : α ∈ (Algebra.adjoin ℂ (Set.range (FreeAlgebra.ι ℂ : L → _))).toSubmodule := by
    rw [FreeAlgebra.adjoin_range_ι]; trivial
  rw [Algebra.adjoin_eq_span] at h1
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h1
  have : ∀ x ∈ Submonoid.closure (Set.range (FreeAlgebra.ι ℂ : L → _)),
      ∃ u : List L, (u.map (FreeAlgebra.ι ℂ)).prod = x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨y, rfl⟩ := hx; exact ⟨[y], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u ++ v, by simp⟩
  choose u hu using fun i => this _ (g i).2
  exact ⟨m, c, u, by rw [← e]; simp only [hu]⟩

theorem lift_words {L M : Type} [AddCommGroup M] [Module ℂ M] (τ : L → Module.End ℂ M) {m : ℕ} (c : Fin m → ℂ)
    (u : Fin m → List L) (x : M) :
    FreeAlgebra.lift ℂ τ (∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod) x =
      ∑ i, c i • (u i).foldr (fun y => τ y) x := by
  have : ∀ l : List L, FreeAlgebra.lift ℂ τ (l.map (FreeAlgebra.ι ℂ)).prod x = l.foldr (fun y => τ y) x := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih => rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]; simp
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, this]

theorem exists_intertwiner {L V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : L → Module.End ℂ V) (hρ : ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤)
    (τ : L → Module.End ℂ M) {d : ℕ} (w : Fin d → V) (m₀ : M)
    (h : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), (∀ a, ∑ i, c i • (u i).foldr (fun y => ρ y) (w a) = 0) →
      ∑ i, c i • (u i).foldr (fun y => τ y) m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[ℂ] M), (∀ a v x, T a (ρ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), T a v = ∑ i, c i • (u i).foldr (fun y => τ y) m₀ := by
  letI : Module (FreeAlgebra ℂ L) V := Module.compHom V (FreeAlgebra.lift ℂ ρ).toRingHom
  letI : Module (FreeAlgebra ℂ L) M := Module.compHom M (FreeAlgebra.lift ℂ τ).toRingHom
  have eV : ∀ (α : FreeAlgebra ℂ L) (v : V), α • v = FreeAlgebra.lift ℂ ρ α v := fun _ _ => rfl
  have eM : ∀ (α : FreeAlgebra ℂ L) (v : M), α • v = FreeAlgebra.lift ℂ τ α v := fun _ _ => rfl
  have cV : ∀ (c : ℂ) (v : V), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eV, AlgHom.commutes]; rfl
  have cM : ∀ (c : ℂ) (v : M), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eM, AlgHom.commutes]; rfl
  have hs : ∀ N : Submodule (FreeAlgebra ℂ L) V, N = ⊥ ∨ N = ⊤ := by
    intro N
    let W : Submodule ℂ V :=
      { carrier := N
        add_mem' := N.add_mem
        zero_mem' := N.zero_mem
        smul_mem' := fun c v hv => by rw [← cV]; exact N.smul_mem _ hv }
    by_cases h0 : W = ⊥
    · left
      rw [eq_bot_iff] at h0 ⊢
      exact fun v hv => h0 (show v ∈ W from hv)
    · right
      have := hρ W (fun x v hv => by
        have := N.smul_mem (FreeAlgebra.ι ℂ x) hv
        rwa [eV, FreeAlgebra.lift_ι_apply] at this) h0
      rw [eq_top_iff] at this ⊢
      exact fun v _ => (show v ∈ W from this trivial)
  haveI : IsSemisimpleModule (FreeAlgebra ℂ L) V := by
    refine (isSemisimpleModule_iff _ _).2 ⟨fun N => ?_⟩
    rcases hs N with rfl | rfl
    exacts [⟨⊤, isCompl_bot_top⟩, ⟨⊥, isCompl_top_bot⟩]
  obtain ⟨T, h1, h2⟩ := exists_hom_of_ann (R := FreeAlgebra ℂ L) w m₀ (by
    intro α hα
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    rw [eM, lift_words]
    refine h m c u fun a => ?_
    rw [← lift_words, ← eV]
    exact congrFun hα a)
  refine ⟨fun a =>
    { toFun := T a
      map_add' := (T a).map_add
      map_smul' := fun c v => by rw [← cV, map_smul, cM]; rfl }, fun a v x => ?_, h1, fun a v => ?_⟩
  · have := (T a).map_smul (FreeAlgebra.ι ℂ x) v
    rwa [eV, eM, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply] at this
  · obtain ⟨α, hα⟩ := h2 a v
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    exact ⟨m, c, u, hα.trans (by rw [eM, lift_words])⟩

theorem exists_maps_of_relations : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  intro hHC n ε H _ _ _ σ hσ d w hw M _ _ τ m₀ h
  have hmem : ∀ (x : Ltr ε) v, IsKFin ε σ v → IsKFin ε σ (ltrV σ x v) := by
    rintro (X | k) v hv
    exacts [isKFin_dRep n ε H σ hσ v hv X.1 X.2, isKFin_translate hv k.2]
  let ρ : Ltr ε → Module.End ℂ (kfin ε σ) := fun x =>
    { toFun := fun v => ⟨ltrV σ x v.1, hmem x v.1 v.2⟩
      map_add' := fun a b => Subtype.ext (by
        rcases x with X | k
        · exact Dw_add hσ.1 (l := [X.1]) (by simpa using X.2) (hσ.2.2.1 _ a.2) (hσ.2.2.1 _ b.2)
        · exact map_add (σ k.1) _ _)
      map_smul' := fun c a => Subtype.ext (by
        rcases x with X | k
        · exact Dw_smul hσ.1 (l := [X.1]) (by simpa using X.2) c (hσ.2.2.1 _ a.2)
        · exact map_smul (σ k.1) _ _) }
  have hword : ∀ (u : List (Ltr ε)) (v : kfin ε σ), (u.foldr (fun y => ρ y) v : kfin ε σ).1 = wordV σ u v.1 := by
    intro u v
    induction u with
    | nil => rfl
    | cons x u ih =>
      show ltrV σ x (u.foldr (fun y => ρ y) v : kfin ε σ).1 = ltrV σ x (wordV σ u v.1)
      rw [ih]
  have hρ : ∀ W : Submodule ℂ (kfin ε σ), (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW h0
    have k1 : ∀ v ∈ W.map (kfin ε σ).subtype, IsKFin ε σ v := by
      rintro _ ⟨v, -, rfl⟩; exact v.2
    have k2 : ∀ (x : Ltr ε), ∀ v ∈ W.map (kfin ε σ).subtype, ltrV σ x v ∈ W.map (kfin ε σ).subtype := by
      rintro x _ ⟨v, hv, rfl⟩; exact ⟨ρ x v, hW x v hv, rfl⟩
    have k3 : ∀ k ∈ Kset ε, ∀ v ∈ W.map (kfin ε σ).subtype, σ k v ∈ W.map (kfin ε σ).subtype :=
      fun k hk => k2 (Sum.inr ⟨k, hk⟩)
    have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hσ.1 hσ.2.1 k1 (fun X hX => k2 (Sum.inl ⟨X, hX⟩)) k3
      (fun e => h0 (Submodule.map_injective_of_injective (kfin ε σ).injective_subtype
        (e.trans (Submodule.map_bot _).symm)))
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, e⟩ := GlobalTheory.HCModIrred.mem_of_dense hσ hd k1 k3 v.2
    exact (Subtype.ext e : y = v) ▸ hy
  obtain ⟨T, h1, h2, h3⟩ := exists_intertwiner ρ hρ τ (fun a => (⟨w a, hw a⟩ : kfin ε σ)) m₀ (by
    intro m c u hu
    refine h m c u fun a => ?_
    have := congrArg Subtype.val (hu a)
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, hword, Submodule.coe_zero] using this)
  choose T' hT' using fun a => LinearMap.exists_extend (T a)
  have e : ∀ a v (hv : IsKFin ε σ v), T' a v = T a ⟨v, hv⟩ := fun a v hv => LinearMap.congr_fun (hT' a) ⟨v, hv⟩
  refine ⟨T', fun a v hv x => ?_, ?_, fun a v hv => ?_⟩
  · rw [e a _ (hmem x v hv), e a v hv]
    exact h1 a ⟨v, hv⟩ x
  · rw [← h2]
    exact Finset.sum_congr rfl fun a _ => e a _ (hw a)
  · rw [e a v hv]
    exact h3 a _

end GlobalTheory.TypeSum.CoefClos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
section
set_option autoImplicit false

namespace GlobalTheory.FinalJoin.RecordRun

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem exists_pageRun_record_sub_four : ∃ CK : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → ∀ (B : WeightFamilies.Prov D) (Q : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B Q j), InR D j → OPO L B → PageRun L X ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP L.Ct (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) :=
  ⟨10, fun _ _ _ T hK S hCnW hg hx hC hCZ B Q _ X hj hO =>
    pageRun_record T hK S hCnW hg hx hC hCZ B Q hj.1 hj.2 X hO⟩

end GlobalTheory.FinalJoin.RecordRun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeWeberRay
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem log_sizes_of_isRay_natCast (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (h2 : Module.finrank ℚ K = 2) (n : ℕ) (hn : 0 < n)
    (hR : IsRay M (Ideal.span {(n : 𝓞 K)})) :
    Real.log (Module.finrank ℚ M) ≤ Real.log (8 * |(discr K : ℝ)|) + 2 * Real.log n ∧
      Real.log |((discr M : ℤ) : ℝ)| / Module.finrank ℚ M ≤
        Real.log (4 * |(discr K : ℝ)|) + Real.log |(discr K : ℝ)| / 2 + 3 * Real.log n := by
  have hq : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  have hE : IsEmpty (K →+* ℝ) := ⟨fun φ =>
    IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) (by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp)⟩
  have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le K M _ hq hR
  rw [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2] at h1
  have hcl := GlobalTheory.classNumber_le_four_mul_abs_discr K h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hr : 0 < Module.finrank K M := Module.finrank_pos
  have hr' : (0 : ℝ) < Module.finrank K M := by exact_mod_cast hr
  have h3 : (Module.finrank K M : ℝ) ≤ 4 * |(discr K : ℝ)| * (n : ℝ) ^ 2 := by
    have : (Module.finrank K M : ℝ) ≤ (classNumber K : ℝ) * (n : ℝ) ^ 2 := by exact_mod_cast h1
    exact this.trans (mul_le_mul_of_nonneg_right hcl (by positivity))
  have h4 : (Module.finrank ℚ M : ℝ) = 2 * Module.finrank K M := by
    rw [← Module.finrank_mul_finrank ℚ K M, h2]; push_cast; ring
  have h5 := Real.log_le_log hr' h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h5
  refine ⟨?_, ?_⟩
  · rw [h4, show 8 * |(discr K : ℝ)| = 2 * (4 * |(discr K : ℝ)|) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (x := 2) (by positivity) (by positivity)]
    push_cast at h5
    linarith
  · have h6 := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal K M n hn (fun 𝔭 h => hR.1 𝔭 (fun hd => h (by
      rwa [Ideal.dvd_span_singleton] at hd)))
    have h7 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal K M _ (Nat.mul_pos hn hr) h6
    rw [h2, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at h7
    push_cast at h5 h7
    linarith

end GlobalTheory.FieldSize
end

