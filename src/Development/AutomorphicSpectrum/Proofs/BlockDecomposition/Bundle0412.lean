import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0268
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0323
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.HighestWeightDifferencesNat
import Development.AutomorphicSpectrum.Definitions.JetCones.Bundle0001
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AutomorphicSpectrum.Proofs.JetProofs.EvFirst
import Development.AutomorphicSpectrum.Proofs.JetProofs.GraphExtend
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfHom
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.HomTrace

theorem finiteDimensional_of_hom (W H : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [Nontrivial W] [FiniteDimensional ℂ (W →ₗ[ℂ] H)] :
    FiniteDimensional ℂ H := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hex : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hcon)
  obtain ⟨φ, hφ⟩ := hex
  let j : H →ₗ[ℂ] (W →ₗ[ℂ] H) :=
    { toFun := fun h => φ.smulRight h
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by
        ext v
        simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hj : Function.Injective j := by
    intro x y hxy
    have h1 : φ w • x = φ w • y := by
      simpa [j] using LinearMap.congr_fun hxy w
    exact smul_right_injective H hφ h1
  exact FiniteDimensional.of_injective j hj

noncomputable def sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    (W →ₗ[ℂ] H) →ₗ[ℂ] (W →ₗ[ℂ] H) where
  toFun f := a ∘ₗ f ∘ₗ b
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

@[simp] theorem sandwich_apply {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) (f : W →ₗ[ℂ] H) :
    sandwich a b f = a ∘ₗ f ∘ₗ b := rfl

theorem trace_sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ W] [FiniteDimensional ℂ H]
    (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W →ₗ[ℂ] H) (sandwich a b) =
      LinearMap.trace ℂ W b * LinearMap.trace ℂ H a := by
  let e := dualTensorHomEquiv ℂ W H
  let M : (TensorProduct ℂ (Module.Dual ℂ W) H) →ₗ[ℂ] (TensorProduct ℂ (Module.Dual ℂ W) H) :=
    TensorProduct.map (Module.Dual.transpose (R := ℂ) b) a
  have hcomp : (e : _ →ₗ[ℂ] _) ∘ₗ M = sandwich a b ∘ₗ (e : _ →ₗ[ℂ] _) := by
    apply TensorProduct.ext'
    intro φ h
    ext v
    simp [e, M, dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
      Module.Dual.transpose_apply]
  have hconj : e.conj M = sandwich a b := by
    rw [LinearEquiv.conj_apply]
    ext1 f
    have := LinearMap.congr_fun hcomp (e.symm f)
    simpa using this
  rw [← hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', LinearMap.trace_transpose']

end GlobalTheory.CompanionTheory.HomTrace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenExists

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_subQuot [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (A B : Subrepresentation ρ) : IsSmooth (subQuot A B) := by
  have stab : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (w : W),
      ∃ H : Subgroup G, ∀ g, g ∈ H ↔ σ g w = w := by
    intro W _ _ σ w
    refine ⟨{ carrier := {g | σ g w = w}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      replace ha : σ a w = w := ha
      replace hb : σ b w = w := hb
      show σ (a * b) w = w
      rw [map_mul, Module.End.mul_apply, hb, ha]
    · show σ 1 w = w
      rw [map_one, Module.End.one_apply]
    · intro a ha
      replace ha : σ a w = w := ha
      show σ a⁻¹ w = w
      conv_lhs => rw [← ha]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro v
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨H₁, hH₁⟩ := stab ρ (x : V)
  obtain ⟨H₂, hH₂⟩ := stab (subQuot A B) (Submodule.Quotient.mk x)
  have hle : H₁ ≤ H₂ := by
    intro g hg
    rw [hH₁] at hg
    rw [hH₂]
    show Submodule.Quotient.mk (A.toRepresentation g x) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hg
  have e₁ : (H₁ : Set G) = {g | ρ g x = x} := Set.ext hH₁
  have e₂ : (H₂ : Set G) = {g | (subQuot A B) g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x} :=
    Set.ext hH₂
  rw [← e₂]
  exact Subgroup.isOpen_mono hle (e₁ ▸ hρ x)

theorem nontrivial_twJacquet_subQuot {ρ : Representation ℂ G V} (N : Subgroup G) (χ : N →* ℂˣ)
    (A B : Subrepresentation ρ) (hB : B.toSubmodule ≤ twKer ρ N χ) (hA : ¬ A.toSubmodule ≤ twKer ρ N χ) :
    Nontrivial (TwJacquet (subQuot A B) N χ) := by
  obtain ⟨a, haA, hak⟩ := SetLike.not_le_iff_exists.mp hA
  let φ : A.toSubmodule →ₗ[ℂ] V ⧸ twKer ρ N χ := (twKer ρ N χ).mkQ ∘ₗ A.toSubmodule.subtype
  have hφ : Submodule.comap A.toSubmodule.subtype B.toSubmodule ≤ LinearMap.ker φ := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (x : V) = (0 : V ⧸ twKer ρ N χ)
    rw [Submodule.Quotient.mk_eq_zero]
    exact hB (Submodule.mem_comap.mp hx)
  let Ψ := (Submodule.comap A.toSubmodule.subtype B.toSubmodule).liftQ φ hφ
  have hker : twKer (subQuot A B) N χ ≤ LinearMap.ker Ψ := by
    apply Submodule.span_le.mpr
    rintro w ⟨n, v, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul]
    show Submodule.Quotient.mk (ρ n (x : V)) - (χ n : ℂ) • Submodule.Quotient.mk (x : V) =
      (0 : V ⧸ twKer ρ N χ)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨n, (x : V), rfl⟩
  refine ⟨⟨(Submodule.Quotient.mk (Submodule.Quotient.mk ⟨a, haA⟩ :
      A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule) :
      _ ⧸ twKer (subQuot A B) N χ), 0, ?_⟩⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h' := hker h
  rw [LinearMap.mem_ker] at h'
  have h'' : Submodule.Quotient.mk a = (0 : V ⧸ twKer ρ N χ) := h'
  exact hak ((Submodule.Quotient.mk_eq_zero _).mp h'')

end General

theorem exists_generic_subQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ →
    IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧
      IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ hfl hgen
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI := hNA.1
  haveI := hNA.2
  have hle : ∀ S T : Subrepresentation ρ, S.asSubmodule ≤ T.asSubmodule ↔ S ≤ T := fun S T => Iff.rfl
  have hsm : StrictMono (fun S : Subrepresentation ρ => S.asSubmodule) := fun S T h =>
    lt_of_le_of_ne ((hle S T).mpr h.le)
      (fun he => h.ne (le_antisymm ((hle S T).mp he.le) ((hle T S).mp he.ge)))
  have wfl : WellFounded (fun S T : Subrepresentation ρ => S < T) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_lt)
  have wfg : WellFounded (fun S T : Subrepresentation ρ => T < S) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_gt)
  have hgen' : Nontrivial (V ⧸ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := hgen
  let T0 : Subrepresentation ρ := ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
  have htop : ¬ T0.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    intro h
    obtain ⟨x, y, hxy⟩ := hgen'.exists_pair_ne
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hxy
    rw [Submodule.Quotient.eq]
    exact h Submodule.mem_top
  obtain ⟨A, hAP, hAmin⟩ := wfl.has_min {A | ¬ A.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N)} ⟨T0, htop⟩
  let Z : Subrepresentation ρ := ⟨⊥, fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]⟩
  have hZk : Z.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := bot_le
  have hZA : Z < A := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0]
      exact A.toSubmodule.zero_mem
    · intro h
      rw [← h] at hAP
      exact hAP hZk
  obtain ⟨B, hBA, hBmax⟩ := wfg.has_min {B | B < A} ⟨Z, hZA⟩
  have hcov : B ⋖ A := ⟨hBA, fun C hBC hCA => hBmax C hCA hBC⟩
  have hBk : B.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    by_contra h
    exact hAmin B h hBA
  exact ⟨A, B, hBA.le, GlobalTheory.SmGL.isIrreducible_subQuot hcov, GlobalTheory.CompanionTheory.GenExists.isSmooth_subQuot hρ A B,
    GlobalTheory.CompanionTheory.GenExists.nontrivial_twJacquet_subQuot _ _ A B hBk hAP⟩

end GlobalTheory.CompanionTheory.GenExists

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing

namespace GlobalTheory.CompanionTheory.KoszulCount

def germSec {X : Scheme.{0}} {L : LB X} (s : L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    X.presheaf.stalk x :=
  X.presheaf.germ (L.U i) x hx (s.f i)

def CotIndep {X : Scheme.{0}} {L : LB X} {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    LinearIndependent (ResidueField (X.presheaf.stalk x))
      (fun j : {j : Fin d // germSec (t j) hx ∈ maximalIdeal (X.presheaf.stalk x)} =>
        ((maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
          CotangentSpace (X.presheaf.stalk x)))

def GoodStalks {X : Scheme.{0}} {L : LB X} (F : X.Modules) {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    RingTheory.Sequence.IsWeaklyRegular (F.presheaf.stalk x :)
        (List.ofFn fun j => germSec (t j) hx) ∧
      Module.length (X.presheaf.stalk x)
        ((F.presheaf.stalk x :) ⧸ (Ideal.span (Set.range fun j => germSec (t j) hx) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))) ≤ 1

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosed
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GroundTheory.Arith.SchemeCoh
namespace GlobalTheory.CompanionTheory.GE

theorem step_integral {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (IH : ∀ J' : X.IdealSheafData, J < J' → Statement I J') : Statement I J := by
  intro E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  letI : J.subscheme.Over (Spec (.of A)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of A))⟩
  have h1 : IsSeparated (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : IsSeparated (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h2 : LocallyOfFiniteType (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : LocallyOfFiniteType (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h3 : QuasiCompact (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : QuasiCompact (J.subschemeι ≫ (X ↘ Spec (.of A))))
  obtain ⟨N, Y, i, O, ψ, W, hi, hψ, hcomm, hW, hiso⟩ := GlobalTheory.T.exists_chow_cover_integral (A := A) (X := J.subscheme)
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩
  have hZ : Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := GlobalTheory.T.formal_existence_projective_open I hI i hi O
  have hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = ((O : Scheme.{0}) ↘ Spec (.of A)) := by
    change (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = O.ι ≫ i ≫ ProjSpace.toSpecBase A N
    rw [hcomm, Category.assoc]
    rfl
  obtain ⟨D, c, J', hDq, hDP, hc, hJ, hkill⟩ := GlobalTheory.T.formal_existence_proper_pushforward I hI J hZ ψ hψ hover W hW hiso hE hS hK hP
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP D hDq c hc
  exact halg (IH J' hJ _ (GlobalTheory.T.coherent_subobject_coherent hE D hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J' D S c' hkill) hP') hDP

theorem statement_bot {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    (X : Scheme.{0}) [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] :
    Statement I (⊥ : X.IdealSheafData) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hwf : WellFoundedGT X.IdealSheafData := GlobalTheory.T.ideal_sheaf_well_founded_gt
  refine WellFoundedGT.induction (motive := fun J : X.IdealSheafData => Statement I J) ⊥ ?_
  intro J IH
  by_cases hJ : J = ⊤
  · subst hJ
    exact GlobalTheory.T.formal_existence_top_ideal I
  rcases GlobalTheory.T.noetherian_ideal_integral_or_split J hJ with h | ⟨J₁, J₂, h₁, h₂, hm⟩
  · exact step_integral I hI J IH
  · exact GlobalTheory.T.formal_existence_product_ideal I J J₁ J₂ hm (IH _ h₁) (IH _ h₂)

theorem geClosed : GEClosed :=
  GlobalTheory.T.geClosed_of_statement_bot fun _ _ _ I hI X _ _ _ _ => statement_bot I hI X

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStable
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem highestWeight_antitone_of_finiteDimensional_stable :
    ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  intro n V _ _ Kf S ν v hG hfd hS hv hv0 hK a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable (ε := fun _ => true) (F := Kf)
      (Formalism.REAL.glRel_kRel (fun _ => true) Kf hG) (ne_of_lt hlt) rfl S (fun y hy => hS b a y hy)
      hv hv0 (hK.1 a) (hK.1 b) (hK.2 a b hlt rfl)
    have hm' : ν a - ν b = (m : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact hm
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

end GlobalTheory.CompanionTheory.RealCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecomposition
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.ExtHw

theorem inner_word_eq_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (hR : Formalism.REAL.GlRel D)
    (hA : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) (Hs : Submodule ℂ H)
    (hs : ∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) {x y : H} (hx : x ∈ Hs) (hy : y ∈ Hs)
    (hxx : ⟪x, x⟫_ℂ = 1) (hyy : ⟪y, y⟫_ℂ = 1) (hxy : ⟪x, y⟫_ℂ = 0)
    (l : List (Fin n × Fin n)) : ⟪x, (l.map fun z => D z.1 z.2).prod y⟫_ℂ = 0 := by
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have vev : ∀ u ∈ Hs, ∀ v ∈ Hs,
      ⟪u, (l.map fun z => D z.1 z.2).prod u⟫_ℂ * ⟪v, v⟫_ℂ =
        ⟪v, (l.map fun z => D z.1 z.2).prod v⟫_ℂ * ⟪u, u⟫_ℂ := fun u hu v hv =>
    GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n (fun _ => true) H H D D μ u v (fun a b c d _ _ => hR a b c d)
      (fun a b c d _ _ => hR a b c d) (fun a b _ => hA a b) (fun a b _ => hA a b)
      (hs u hu) (hs v hv) l (fun _ _ => rfl)
  generalize (l.map fun z => D z.1 z.2).prod = W at vev ⊢
  have h1 := vev x hx y hy
  have h2 := vev (x + y) (Hs.add_mem hx hy) x hx
  have h3 := vev (x + Complex.I • y) (Hs.add_mem hx (Hs.smul_mem _ hy)) x hx
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hxx, hyy, hxy, hyx, Complex.conj_I] at h1 h2 h3
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h4 : ⟪x, W y⟫_ℂ + ⟪y, W x⟫_ℂ = 0 := by linear_combination h2 + h1
  have h5 : Complex.I * (⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ) = 0 := by
    linear_combination h3 + h1 + (⟪y, W y⟫_ℂ - ⟪x, W x⟫_ℂ) * hI
  have h6 : ⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ = 0 :=
    (mul_eq_zero.1 h5).resolve_left Complex.I_ne_zero
  linear_combination (1 / 2 : ℂ) * h4 + (1 / 2 : ℂ) * h6

theorem kmap_extend : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H) (D' : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ), Formalism.REAL.GlRel D → Formalism.REAL.GlRel D' → (∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) → (∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ) → ∀ Hs : Submodule ℂ H, (∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) → ∀ f : Hs →ₗ[ℂ] V, (∀ x, Formalism.REAL.KHighest (fun _ => true) D' μ (f x)) → ∃ T : H →ₗ[ℂ] V, (∀ x : Hs, T x = f x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  intro n H V _ _ _ _ _ D D' μ hR hR' hA hA' Hs hs f hf
  let ξ := stdOrthonormalBasis ℂ Hs
  have hself : ∀ i, ⟪(ξ i : H), (ξ i : H)⟫_ℂ = 1 := fun i => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i i
    rw [if_pos rfl] at this
    exact this
  have hoff : ∀ i j, i ≠ j → ⟪(ξ i : H), (ξ j : H)⟫_ℂ = 0 := fun i j hij => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i j
    rw [if_neg hij] at this
    exact this
  have hne : ∀ i, (ξ i : H) ≠ 0 := fun i h0 => by
    have := hself i
    rw [h0, inner_zero_left] at this
    exact zero_ne_one this
  have hex : ∀ i, ∃ T : H →ₗ[ℂ] V, T (ξ i : H) = f (ξ i) ∧ GlobalTheory.CompanionTheory.AlgRepEndIrreducible.KMap (fun _ => true) D D' T :=
    fun i => GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.hwmap n (fun _ => true) H V D D' μ (ξ i : H) (f (ξ i))
      (fun a b c d _ _ => hR a b c d) (fun a b c d _ _ => hR' a b c d)
      (fun a b _ => hA a b) (fun a b _ => hA' a b) (hs _ (ξ i).2) (hf _) (hne i)
  choose Ti hTi hTK using hex
  let Z : _ → Submodule ℂ H := fun i => Submodule.span ℂ
    (Set.range fun l : List (Fin n × Fin n) => (l.map fun z => D z.1 z.2).prod (ξ i : H))
  have hst : ∀ i a b, ∀ z ∈ Z i, D a b z ∈ Z i := by
    intro i a b z hz
    induction hz using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact Submodule.subset_span ⟨(a, b) :: l, by simp⟩
  have hperp : ∀ i a b, ∀ z ∈ (Z i)ᗮ, D a b z ∈ (Z i)ᗮ := by
    intro i a b z hz
    rw [Submodule.mem_orthogonal] at hz ⊢
    intro u hu
    rw [← hA b a]
    exact hz _ (hst i b a u hu)
  have hcomm : ∀ i a b w, (Z i).starProjection (D a b w) = D a b ((Z i).starProjection w) := by
    intro i a b w
    obtain ⟨u, hu, z, hz, rfl⟩ := (Z i).exists_add_mem_mem_orthogonal w
    have e1 : (Z i).starProjection u = u := Submodule.starProjection_eq_self_iff.2 hu
    have e2 : (Z i).starProjection z = 0 := (Submodule.starProjection_apply_eq_zero_iff _).2 hz
    have e3 : (Z i).starProjection (D a b u) = D a b u :=
      Submodule.starProjection_eq_self_iff.2 (hst i a b u hu)
    have e4 : (Z i).starProjection (D a b z) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).2 (hperp i a b z hz)
    rw [map_add, map_add, map_add, e1, e2, e3, e4, add_zero, add_zero]
  have hdiag : ∀ i, (Z i).starProjection (ξ i : H) = ξ i := fun i =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span ⟨[], by simp⟩)
  have hzero : ∀ i j, i ≠ j → (Z i).starProjection (ξ j : H) = 0 := by
    intro i j hij
    refine (Submodule.starProjection_apply_eq_zero_iff _).2 ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.word_adj (ε := fun _ => true) (fun a b _ => hA a b) l (fun _ _ => rfl)]
      exact inner_word_eq_zero D μ hR hA Hs hs (ξ i).2 (ξ j).2 (hself i) (hself j) (hoff i j hij) _
  let T : H →ₗ[ℂ] V := ∑ i, (Ti i).comp ((Z i).starProjection : H →L[ℂ] H).toLinearMap
  have hTapp : ∀ w, T w = ∑ i, Ti i ((Z i).starProjection w) := fun w => by
    simp [T, LinearMap.sum_apply]
  refine ⟨T, ?_, ?_⟩
  · have hb : T.comp Hs.subtype = f := by
      refine ξ.toBasis.ext fun j => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, Submodule.subtype_apply, hTapp,
        Finset.sum_eq_single j]
      · rw [hdiag, hTi]
      · intro i _ hij
        rw [hzero i j hij, map_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    intro x
    exact LinearMap.congr_fun hb x
  · intro a b w
    rw [hTapp, hTapp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, hTK i a b rfl]

end GlobalTheory.CompanionTheory.RealCount.ExtHw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL k) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | exact GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterleavingTwoColourEmbeddingStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interleaving_two_colour_embedding : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w → ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length) (σ₁ : Fin v.length ↪o Fin w.length), (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧ (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings | exact GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings | (intros; apply GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetCuspidalSupportOfFunctionalStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_cuspidal_support_of_functional : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n) (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ), f ≠ 0 → (∀ t w, f (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) = PositivityTheory.Lbc.torusChar ξ t * f w) → ∃ g : (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.CharTensor.chartotensor | exact GlobalTheory.CompanionTheory.CharTensor.chartotensor | (intros; apply GlobalTheory.CompanionTheory.CharTensor.chartotensor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAdmissibleFixedStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_admissible_fixed : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → PositivityTheory.Lbc.C0 k → PositivityTheory.Lbc.C3 k → ∀ m, 1 ≤ m → FiniteDimensional ℂ ↥(fixed (jac (stdBlocks (fun _ : Fin n => 1) hd) π) (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd)) := by
  first | exact @GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac | exact GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac | (intros; apply GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac <;> assumption)
end

