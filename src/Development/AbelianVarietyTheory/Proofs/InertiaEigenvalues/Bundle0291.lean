import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpenStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRep_ker_isOpen : ∀ (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by
  first | exact @GlobalTheory.TypeLeaf.redF_ker_isOpen | exact GlobalTheory.TypeLeaf.redF_ker_isOpen | (intros; apply GlobalTheory.TypeLeaf.redF_ker_isOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllLeInf
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology Pointwise

namespace GlobalTheory.SelInfl

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))} {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M) (A : Places F Ω)

theorem vanish {f : G F Ω → M} (hf : f ∈ Z1 (rhoS.comp (toGS Ω S) : Representation R (G F Ω) M))
    (hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), f g = rhoS (toGS Ω S g) m - m) (n : G F Ω)
    (hn : n ∈ NS Ω S) : f n = 0 := by
  obtain ⟨hfc, hfco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ f).1 hf
  have ht : ∀ g ∈ NS Ω S, toGS Ω S g = 1 := fun g hg => (QuotientGroup.eq_one_iff g).2 hg
  have hρ : ∀ g ∈ NS Ω S, ∀ x : M, (rhoS.comp (toGS Ω S)) g x = x := by
    intro g hg x
    rw [MonoidHom.comp_apply, ht g hg, map_one, Module.End.one_apply]
  have h1 : f 1 = 0 := by
    have := hfco 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    simpa using this
  have hinv : ∀ a ∈ NS Ω S, f a = 0 → f a⁻¹ = 0 := by
    intro a ha h0
    have := hfco a a⁻¹
    rw [mul_inv_cancel, h1, h0, zero_add, hρ a ha] at this
    exact this.symm
  let H : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ f g = 0}
      one_mem' := ⟨(NS Ω S).one_mem, h1⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨(NS Ω S).mul_mem ha.1 hb.1, by rw [hfco, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨(NS Ω S).inv_mem ha.1, hinv a ha.1 ha.2⟩ }
  have hconj : ∀ n ∈ H, ∀ g : G F Ω, g * n * g⁻¹ ∈ H := by
    intro n hn g
    refine ⟨(normal_NS S).conj_mem n hn.1 g, ?_⟩
    have e1 := hfco (g * n) g⁻¹
    have e2 := hfco g n
    have e3 := hfco g g⁻¹
    rw [map_mul, Module.End.mul_apply, hρ n hn.1, e2, hn.2, map_zero, add_zero] at e1
    rw [mul_inv_cancel, h1] at e3
    rw [e1, ← e3]
  have hHn : H.Normal := ⟨hconj⟩
  have hclosed : IsClosed (H : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter (isClosed_singleton.preimage hfc)
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A' ∈ {A' : ValuationSubring Ω | IsPlaceOver A' v}, Inertia (F := F) A') ⊆ H := by
    intro σ hσ
    have hσN : σ ∈ NS Ω S :=
      Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ
    obtain ⟨v, hv, A', hA', hσA'⟩ := hσ
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hA'
    have hσI : σ ∈ Ine (F := F) (γ • A.1 v) := by
      rw [hγ]
      exact mem_Ine.2 hσA'
    have hτ := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσI
    have hτN : γ⁻¹ * σ * γ ∈ NS Ω S := by
      have := (normal_NS S).conj_mem σ hσN γ⁻¹
      rwa [inv_inv] at this
    obtain ⟨m, hm⟩ := hv0 v hv
    have hfτ : f (γ⁻¹ * σ * γ) = 0 := by
      rw [hm _ hτ, ht _ hτN, map_one, Module.End.one_apply, sub_self]
    have := hconj _ ⟨hτN, hfτ⟩ γ
    have e : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ := by group
    rw [e] at this
    exact this
  have hle : NS Ω S ≤ H :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hclosed
  exact (hle hn).2

theorem selAllLeInf : Formalism.GaloisCohomology.SelAllLeInf := by
  intro F Ω _ _ _ _ _ S R _ M _ _ _ _ _ _ rhoS _ A L hL x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hloc := (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).1 hx
  have hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), z.1 g = rhoS (toGS Ω S g) m - m := by
    intro v hv
    have h1 := hL v hv (hloc v)
    have h2 : (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))).subtype
        continuous_subtype_val (restrictCocycles1 _ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val z)) :
        H1 _) = 0 := h1
    have h3 := (Submodule.Quotient.mk_eq_zero _).1 h2
    rw [Submodule.mem_comap] at h3
    obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 h3
    refine ⟨m, fun g hg => ?_⟩
    have gD : g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hg
    have gJ : (⟨g, gD⟩ : Dec (F := F) (A.1 v)) ∈ (Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    exact hm ⟨⟨g, gD⟩, gJ⟩
  have hvan : ∀ n ∈ NS Ω S, z.1 n = 0 := fun n hn => vanish rhoS A z.2 hv0 n hn
  obtain ⟨hzc, hzco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 z.2
  have hwd : ∀ a b : G F Ω, a⁻¹ * b ∈ NS Ω S → z.1 a = z.1 b := by
    intro a b hab
    have := hzco a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hvan _ hab, map_zero, add_zero] at this
    exact this.symm
  let z' : GS Ω S → M := fun q =>
    Quotient.liftOn' q z.1 (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.1 hab))
  have hz'c : Continuous z' := Continuous.quotient_liftOn' hzc _
  have hz'co : ∀ p q : GS Ω S, z' (p * q) = z' p + rhoS p (z' q) := by
    intro p q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact hzco a b
  let w : Z1 rhoS := ⟨z', (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).2 ⟨hz'c, hz'co⟩⟩
  exact ⟨Submodule.Quotient.mk w, rfl⟩

end GlobalTheory.SelInfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResiduesStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senWeight_subquotient_model_mem_residues : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  first | exact @GlobalTheory.Models.ModTh.sen_model_subquot_mem_U | exact GlobalTheory.Models.ModTh.sen_model_subquot_mem_U | (intros; apply GlobalTheory.Models.ModTh.sen_model_subquot_mem_U <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShiftedJumpUpperBoundLeTwistBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  first | exact @GlobalTheory.hS_le_bound | exact GlobalTheory.hS_le_bound | (intros; apply GlobalTheory.hS_le_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecPrOfZSpecTypeTie
section
noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin.SpecProj

theorem le_iSup_of_dichotomy {V ι : Type} [AddCommGroup V] [Module ℂ V] (T : ι → Submodule ℂ V) (A B : Submodule ℂ V)
    (hd : Disjoint A B) (ht : ⨆ P, T P = ⊤) (h : ∀ P, T P ≤ A ∨ T P ≤ B) : A ≤ ⨆ P ∈ {P | T P ≤ A}, T P := by
  intro x hx
  have hle : (⊤ : Submodule ℂ V) ≤ (⨆ P ∈ {P | T P ≤ A}, T P) ⊔ B := by
    rw [← ht]
    refine iSup_le fun P => (h P).elim (fun hP => le_sup_of_le_left ?_) le_sup_of_le_right
    exact le_biSup T (show P ∈ {P | T P ≤ A} from hP)
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle (Submodule.mem_top (x := x)))
  have ha' : a ∈ A := (iSup₂_le fun P hP => hP : (⨆ P ∈ {P | T P ≤ A}, T P) ≤ A) ha
  have hb0 : b = 0 := Submodule.disjoint_def.1 hd b (by rw [← add_sub_cancel_left a b, e]; exact A.sub_mem hx ha') hb
  rw [← e, hb0, add_zero]; exact ha

theorem specPr_of_zSpec_typeTie : ∀ (D : D7) (i : D.nd.Loc), ZSpec D i → TypeTie D i → SpecPr D i := by
  intro D i hZ hT
  have hd := (Idx.Z0 D (D.nd.mu i) (D.nd.j i)).orthogonal_disjoint
  have mono : ∀ {Y Y' : Set (D.nd.X i)}, Y ⊆ Y' → D.nd.eigSum i Y ≤ D.nd.eigSum i Y' := fun h => biSup_mono h
  constructor
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd (D.naut.typeV_top i) (fun P => (hZ P).1) hy))
    rintro x ⟨P, hP, hx⟩
    by_contra hn
    exact D.naut.typeV_ne i P (hd hP (((hZ P).2 x hx).2 hn) |> le_bot_iff.1)
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd.symm (D.naut.typeV_top i) (fun P => (hZ P).1.symm) hy))
    rintro x ⟨P, hP, hx⟩ hn
    exact D.naut.typeV_ne i P (hd (((hZ P).2 x hx).1 hn) hP |> le_bot_iff.1)

end GlobalTheory.EtaJoin.SpecProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TameDesign
open scoped Pointwise

private theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

section General

variable {Γ R : Type} [Group Γ] [CommRing R]

private theorem mem_ker_char_iff (J : Ideal R) (χ : Γ →* Rˣ) (g : Γ) :
    g ∈ ((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker ↔ ((χ g : Rˣ) : R) - 1 ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  rfl

private theorem isOpen_ker_char [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (χ : Γ →* Rˣ)
    (hχ : Continuous fun g => ((χ g : Rˣ) : R)) :
    IsOpen (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) := by
  have : (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) =
      (fun g => ((χ g : Rˣ) : R) - 1) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_char_iff, Set.mem_preimage]
  rw [this]
  exact hJ.preimage (hχ.sub continuous_const)

end General

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

omit [TopologicalSpace R] [IsTopologicalRing R] in
private theorem eq_zero_of_mem_pow (x : R) (h : ∀ m, x ∈ IsLocalRing.maximalIdeal R ^ (m + 1)) : x = 0 := by
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
  exact fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (h m)

private theorem char_eq_one_of_wild (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hA : IsPlaceOver A v) (n : ℕ)
    (hv : ((n : ℕ) : 𝓞 E) ∉ v.asIdeal) (χ : Formalism.ConjugateSelfDual.G E Ω →* Rˣ) (hχ : Continuous fun g => ((χ g : Rˣ) : R))
    (σ : Formalism.ConjugateSelfDual.G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (h1 : χ σ ^ n = 1) : χ σ = 1 := by
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  refine eq_zero_of_mem_pow _ fun m => ?_
  rw [← mem_ker_char_iff]
  refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal E Ω A v hA _ inferInstance
    (isOpen_ker_char _ ((isAdic_iff.mp hR).1 _) χ hχ) σ n hv hσ ?_
  rw [mem_ker_char_iff, map_pow, h1]
  simp

end Wild

theorem firstLocalChar_wild_eq_one_away_from_l (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hvl : v ∉ placesOver D.host.E (D.nd.l i)) (σ : GE D.nd) (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) :
    D.nd.chi i 1 σ = 1 := by
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := wild_mem_Ine hσ
  have hvl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by rwa [D.ntw.twOf_l]

  have hψ : D.ntw.psiL i σ = 1 := by
    obtain ⟨n, hn⟩ := D.ntw.psiL_ord i σ
    have hmem := GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ (D.nd.plOm.1 v) v hA (D.ntw.psiL i).ker
      inferInstance (D.ntw.psiL_open i) σ (D.nd.l i ^ n) ?_ hσ (by rw [MonoidHom.mem_ker, map_pow, hn])
    · exact hmem
    · intro h
      apply hvl
      have hp : (D.nd.l i).Prime := Fact.out
      exact v.isPrime.mem_of_pow_mem n (by simpa using h)

  have hc : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) σ = 1 := by
    by_cases hpD : v ∈ D.ntw.pD (D.ntw.twOf i)
    · have h15 := D.ntw.delta_15 (D.ntw.twOf i) v hpD _ hA
      have hd : D.ntw.delta (D.ntw.twOf i) σ ^ 15 = 1 := by
        have h := pow_card_eq_one'
          (G := (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.ntw.delta (D.ntw.twOf i)))
          (x := ⟨_, σ, hI, rfl⟩)
        rw [h15] at h
        exact congrArg Subtype.val h
      have h15v : ((15 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
        intro h
        have hN := D.ntw.delta_tame (D.ntw.twOf i) v hpD
        have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := Ideal.absNorm_mem _
        have e : Ideal.absNorm v.asIdeal = 15 * (Ideal.absNorm v.asIdeal / 15) + 1 := by omega
        rw [e] at hm
        push_cast at hm
        have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
          have := v.asIdeal.sub_mem hm (v.asIdeal.mul_mem_right (((Ideal.absNorm v.asIdeal / 15 : ℕ)) : 𝓞 D.host.E) (by simpa using h))
          simpa using this
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      refine char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA 15 h15v _
        (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ ?_
      rw [D.ntw.twistCharacterFamily_at_auxiliaryPlaces _ _ _ v hpD _ hA σ hI]
      split_ifs
      · exact hd
      · rw [inv_pow, hd, inv_one]
    · by_cases hg : ∃ k, v ∈ placesOver D.host.E (D.host.g k)
      · obtain ⟨k, hvg⟩ := hg
        have hg1 : ((D.host.g k - 1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun hm => by
          refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
          have := v.asIdeal.sub_mem hvg hm
          rwa [Nat.cast_sub (D.host.g_prime k).one_le, Nat.cast_one, sub_sub_cancel] at this
        exact char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA _ hg1 _
          (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ (D.ntw.twistCharacterFamily_tame _ _ _ k v hvg hvl' _ hA σ hI)
      · push_neg at hg
        exact D.ntw.twistCharacterFamily_unramified _ _ _ v hvl' hg hpD _ hA σ hI
  rw [D.ntw.chi_tw i]
  simp [hψ, hc]

theorem main : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  intro D i
  have hc : TameCharacterConditions D i := by
    refine ⟨fun v hv σ hσ => GlobalTheory.TameDesign.firstLocalChar_wild_eq_one_away_from_l D i v ?_ σ hσ, Formalism.MainNotions.SumRepresentations.Del_holds D i⟩
    rcases hv with hQ | ⟨hS, -⟩
    · exact D.nd.SQ_l i v (Or.inr hQ)
    · exact D.nd.SQ_l i v (Or.inl hS)
  exact ⟨hc, galois_condition_five_extra_of D i hc⟩

end GlobalTheory.TameDesign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGeneratorImageEqCoprimePowStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameGenerator_image_eq_coprime_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ γ' : G E Ω), TameGenAt A γ → TameGenAt A γ' → ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) → ∃ n : ℕ, n.Coprime (orderOf (φ γ)) ∧ 0 < orderOf (φ γ) ∧ φ γ' = φ γ ^ n := by
  first | exact @GlobalTheory.TypeLeaf.tameGen_pow | exact GlobalTheory.TypeLeaf.tameGen_pow | (intros; apply GlobalTheory.TypeLeaf.tameGen_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.TameScalar

theorem not_mem_placesOver {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro hv'
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnit_inv_sq_sub_one {O : Type} [CommRing O] (u : Oˣ) (h : IsUnit ((u : O) ^ 2 - 1)) :
    IsUnit (((u⁻¹ : Oˣ) : O) ^ 2 - 1) := by
  have e : ((u⁻¹ : Oˣ) : O) ^ 2 - 1 = -(((u⁻¹ : Oˣ) : O) ^ 2 * ((u : O) ^ 2 - 1)) := by
    rw [mul_sub, ← mul_pow, Units.inv_mul]; ring
  rw [e]
  exact (((u⁻¹).isUnit.pow 2).mul h).neg

theorem isUnit_sub_one {O : Type} [CommRing O] (x : O) (h : IsUnit (x ^ 2 - 1)) : IsUnit (x - 1) := by
  have e : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

theorem exists_scalar_tmat_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  intro D N X bkP i s z h hz
  obtain ⟨v, hv, A, hA, hzA, hu, -⟩ := hz
  have hlp : (X.l i).Prime := (X.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (X.l i) := by
    refine not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have h1 : X.rhoS i s z = 1 := h.1 v hl hg A hA z hzA
  have h2 : chiS i s z = if X.side i s then X.delta i z else (X.delta i z)⁻¹ :=
    X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
  have h3 : IsUnit ((((chiS i s z)⁻¹ : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) := by
    rw [h2]
    split_ifs
    · exact isUnit_inv_sq_sub_one _ hu
    · rw [inv_inv]; exact hu
  refine ⟨(chiS i s z)⁻¹, ?_, h3, isUnit_sub_one _ h3, ?_⟩
  · rw [Tmat, h1, Units.val_one]
  · have h4 : cycZ D.host.E N.Om (X.l i) z = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
      rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
      simp
    simp [eps0, h4]

end GlobalTheory.TwSys.TameScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEstimateGaloisEigenvectorCLTate
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem tate_eigenvector_estimate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  intro l _ γ u y z N e δ hy hu hz he hT hδ
  have hca : ∀ c : ℚ_[l], ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c :=
    fun _ => rfl
  have hn : ∀ c : ℚ_[l], ‖algebraMap ℚ_[l] ℂ_[l] c‖ = ‖c‖ := fun c => by
    rw [← hca, PadicComplex.norm_extends, norm_algebraMap']
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  set U : ℂ_[l] := algebraMap ℚ_[l] ℂ_[l] u with hU
  have hv : ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ ≤ e := by
    rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
      hca, ← GlobalTheory.RingBasics.σC_coe]
    have h1 : Per.σC γ (z : ℂ_[l]) - U * (z : ℂ_[l])
        = U * (y - (z : ℂ_[l])) + -Per.σC γ (y - (z : ℂ_[l])) := by
      rw [map_sub, hy]; ring
    rw [← hU, h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hU, hn, hu, one_mul]; exact he
    · rw [norm_neg, GlobalTheory.RingBasics.norm_σC]; exact he
  have hpow : ∀ i : ℕ, Per.σC (γ ^ i) y = U ^ i * y := by
    intro i
    induction i with
    | zero => simp [GlobalTheory.RingBasics.σC_one]
    | succ i ih =>
      rw [pow_succ, GlobalTheory.RingBasics.σC_mul, hy, map_mul, hU, TateTwist.σC_algebraMap, ← hU, ih]
      ring
  have htel : ∑ i ∈ Finset.range N, (γ ^ i) (γ z) = ∑ i ∈ Finset.range N, (γ ^ i) z := by
    have h := Finset.sum_range_sub (fun i => (γ ^ i) z) N
    rw [Finset.sum_sub_distrib] at h
    simp only [hz, pow_zero, AlgEquiv.one_apply, sub_self, pow_succ, AlgEquiv.mul_apply] at h
    exact sub_eq_zero.1 h
  have hTv : ∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)
      = algebraMap ℚ_[l] (Om l) (1 - u) * ∑ i ∈ Finset.range N, (γ ^ i) z := by
    simp only [map_sub, map_mul, AlgEquiv.commutes, Finset.sum_sub_distrib, htel, map_one,
      ← Finset.mul_sum]
    ring
  set S : Om l := ∑ i ∈ Finset.range N, (γ ^ i) z with hS
  have hSc : (S : ℂ_[l]) = ∑ i ∈ Finset.range N, Per.σC (γ ^ i) (z : ℂ_[l]) := by
    simp only [GlobalTheory.RingBasics.σC_coe]
    exact map_sum (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) _ _
  have hB : ‖(U - 1) * (S : ℂ_[l])‖ ≤ δ * e := by
    have h2 : (U - 1) * (S : ℂ_[l]) = -((algebraMap ℚ_[l] (Om l) (1 - u) * S : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_mul, hca, map_sub, map_one, ← hU]; ring
    rw [h2, norm_neg, PadicComplex.norm_extends, ← hTv]
    exact hT.trans (mul_le_mul_of_nonneg_left hv hδ)
  have hA : ‖∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))‖ ≤ e :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he0 fun i _ => by
      rw [GlobalTheory.RingBasics.norm_σC]; exact he
  have hmain : algebraMap ℚ_[l] ℂ_[l] (u ^ N - 1) * y
      = (U - 1) * (∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))) + (U - 1) * (S : ℂ_[l]) := by
    rw [hSc, ← mul_add, ← Finset.sum_add_distrib]
    simp only [map_sub, sub_add_cancel, hpow, map_pow, map_one, ← hU]
    rw [← Finset.sum_mul, ← mul_assoc, mul_geom_sum]
  rw [← hn, ← norm_mul, hmain]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ hB)
  have h3 : ‖U - 1‖ = ‖u - 1‖ := by rw [← hn, map_sub, map_one]
  rw [norm_mul, h3]
  exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_H2_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  first | exact @GlobalTheory.TateTop.tateH2_of_duality_loc | exact GlobalTheory.TateTop.tateH2_of_duality_loc | (intros; apply GlobalTheory.TateTop.tateH2_of_duality_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerateStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c ∈ BQ LA _ hI) ∧ (∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ quotientCocycles LA _ hI, CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c' ∈ BQ LA' _ hI') := by
  first | exact @GlobalTheory.TateFin.tate_pairing_nondegenerate | exact GlobalTheory.TateFin.tate_pairing_nondegenerate | (intros; apply GlobalTheory.TateFin.tate_pairing_nondegenerate <;> assumption)
end

