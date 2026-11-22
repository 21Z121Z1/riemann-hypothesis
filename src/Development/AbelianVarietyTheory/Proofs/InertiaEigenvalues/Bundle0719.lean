import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.LubinTateReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionRankinSelberg
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtDual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (w.adicCompletion E) → WD h}

theorem nu_eq (H : CuspLaws a ha e r) {x : IrrGL (w.adicCompletion E)} (hx : x.IsCusp) (s : ℝ) :
    r (x.nu s) = (r x).lpTw s := by
  rw [IrrGL.nu, H.twist x hx, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem summand_dual (H : CuspLaws a ha e r) {Δ Δ' : Segment (w.adicCompletion E)} (hd : SegDual Δ Δ') :
    ((r Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ'.len) =
      (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).lpDual := by
  obtain ⟨hl, hD⟩ := hd
  have hc : (Δ.first.nu ((Δ.len : ℂ) - 1)).IsCusp := Δ.isCusp_first.nu _
  have e1 := H.dual _ _ hc Δ'.isCusp_first hD
  have e2 : Δ.first.nu ((Δ.len : ℂ) - 1) = Δ.first.nu (((Δ.len : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e2, nu_eq H Δ.isCusp_first] at e1
  obtain ⟨hS, hT, hP⟩ := GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h
  rw [e1, hl, hP, hT, hT, WD.lpTw_add]
  congr 2
  ring

theorem map_summand_dual (H : CuspLaws a ha e r) {l l' : List (Segment (w.adicCompletion E))}
    (hF : List.Forall₂ SegDual l l') :
    l'.map (fun Δ => ((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)) =
      l.map (fun Δ => (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).lpDual) := by
  induction hF with
  | nil => rfl
  | cons hd _ ih => rw [List.map_cons, List.map_cons, ih, summand_dual H hd]

end GlobalTheory.LocLanglands.ExtDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionGaloisActionStatement
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_torsion_galois_action : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra K Ω]
    [ValuativeExtension K Ω] [IsSepClosure K Ω] {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}
    (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (k : ℤ) (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)),
    x ∈ lubinTateTorsion Ω (hπ := hπ) hf n →
    ∃ hz : x.val ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K Ω (unitUniformizerPow hπ u k) ⟨x.val, hz⟩ : maximalAbelianExtension K Ω) : Ω) =
        (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  first | exact @GlobalTheory.localArtinMap_unitUniformizerPow_lubinTateTorsion | exact GlobalTheory.localArtinMap_unitUniformizerPow_lubinTateTorsion | (intros; apply GlobalTheory.localArtinMap_unitUniformizerPow_lubinTateTorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → IsIntM (frMapO S T F.βS F.βT x) → x ∈ F.lat := by
  first | exact @GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int | exact GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int | (intros; apply GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem invT_val_eq (g : GA E a) : (invT a (Ad E) g).val = (g.valᵀ)⁻¹ := by
  change (g⁻¹).valᵀ = _
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]

theorem invT_scalar {R : Type} [CommRing R] (z : Rˣ) :
    invT a R (GeneralLinearGroup.scalar (Fin a) z) = GeneralLinearGroup.scalar (Fin a) z⁻¹ := by
  apply Units.ext
  change ((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _
  rw [← map_inv]
  ext i j
  by_cases h : i = j
  · subst h; simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h, Ne.symm h]

namespace CuspSub

variable (π : CuspSub E a)

def contra : CuspSub E a := UpperTheory.V.TC.dual π

@[simp] theorem contra_contra : π.contra.contra = π := UpperTheory.V.TC.dual_dual π

variable {π} {π' : CuspSub E a}

theorem Iso.contra (h : Iso π π') : Iso π.contra π'.contra := UpperTheory.V.TC.iso_dual h

theorem HasCentral.contra {ω : HChar E} (h : π.HasCentral ω) : π.contra.HasCentral ω⁻¹ := by
  rintro z _ ⟨ψ, hψ, rfl⟩
  change rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ
  rw [UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]
  congr 1
  simp

theorem IsUnitary.contra (h : π.IsUnitary) : π.contra.IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨ω⁻¹, h1.inv, h2.contra⟩

theorem HasSatGL.contra {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : HasSatGL w (π.locRep w) B) :
    HasSatGL w (π.contra.locRep w) (B.map (·⁻¹)) := UpperTheory.V.TC.hasSatGL_dual h

end CuspSub

namespace CG

def contra (π : CG E a) : CG E a :=
  Quotient.map (sa := CuspSub.setoid E a) (sb := CuspSub.setoid E a) CuspSub.contra (fun _ _ h => h.contra) π

@[simp] theorem contra_mk (π : CuspSub E a) : (mk π).contra = mk π.contra := rfl

theorem IsUnitary.contra {π : CG E a} (h : π.IsUnitary) : π.contra.IsUnitary := by
  induction π using Quotient.inductionOn with
  | _ π => exact (isUnitary_mk π.contra).2 ((isUnitary_mk π).1 h).contra

theorem HasSat.contra {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) :
    π.contra.HasSat w (B.map (·⁻¹)) := by
  induction π using Quotient.inductionOn with
  | _ π => exact CuspSub.HasSatGL.contra h

@[simp] theorem contra_contra (π : CG E a) : π.contra.contra = π := by
  induction π using Quotient.inductionOn with
  | _ π => exact congrArg mk π.contra_contra

end CG

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHyperplaneAverageSupportResidueGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

section Reindex
variable {n K L : Type} [Fintype n] [CommRing K] [CommRing L]

theorem map_symm_mulVec_comp (ρ : K ≃+* L) (M : Matrix n n L) (x : n → L) :
    (M.map ρ.symm) *ᵥ (fun j => ρ.symm (x j)) = fun j => ρ.symm ((M *ᵥ x) j) := by
  funext j
  exact (RingHom.map_mulVec ρ.symm.toRingHom M x j).symm

theorem fix_hyperplane_map_iff (ρ : K ≃+* L) (M : Matrix n n L) (a : n → K) :
    (∀ x, (fun j => ρ (a j)) ⬝ᵥ x = 0 → M *ᵥ x = x) ↔ ∀ w, a ⬝ᵥ w = 0 → (M.map ρ.symm) *ᵥ w = w := by
  constructor
  · intro h w hw
    have hd : (fun j => ρ (a j)) ⬝ᵥ (fun j => ρ (w j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.toRingHom a w).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hw, map_zero] at this
      exact this
    have h1 := h _ hd
    have h2 := map_symm_mulVec_comp ρ M (fun j => ρ (w j))
    rw [h1] at h2
    simpa only [RingEquiv.symm_apply_apply] using h2
  · intro h x hx
    have hd : a ⬝ᵥ (fun j => ρ.symm (x j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.symm.toRingHom (fun j => ρ (a j)) x).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx, map_zero] at this
      simpa only [Function.comp_def, RingEquiv.symm_apply_apply] using this
    have h1 := h _ hd
    rw [map_symm_mulVec_comp] at h1
    funext j
    have := congrArg ρ (congrFun h1 j)
    simpa only [RingEquiv.apply_symm_apply] using this

end Reindex

theorem mirC_hyperplane_reindex : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (v : FinPl D) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP) (a : Fin D.R.r → IsLocalRing.ResidueField (OI v)) (F : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ), (∑ᶠ g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0}, F (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) = ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, F g := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP hPP v ρk a F
  set P : R.Pg := ⟨PP, hPP⟩ with hP
  have key : ∀ g : G, ((∀ x, (fun j => ρk (a j)) ⬝ᵥ x = 0 →
      ((R.eG g P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) *ᵥ x = x) ↔
      ∀ w, a ⬝ᵥ w = 0 → ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w) :=
    fun g => fix_hyperplane_map_iff ρk _ a
  have hset : {g : G | mirC R i P (fun j => ρk (a j)) false 1 g ≠ 0} =
      {g : G | (∀ PP', PP' ≠ P → R.eG g PP' = 1) ∧ ∀ w, a ⬝ᵥ w = 0 →
        ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w} := by
    ext g
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← key g]
    simp only [mirC, Bool.false_eq_true, ↓reduceIte, zpow_one]
    split_ifs with hc
    · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]
      exact hc
    · simp only [ne_eq, not_true_eq_false, false_iff]
      exact hc
  rw [hset]
  apply finsum_mem_eq_of_bijOn (fun g => Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P))
  · refine ⟨?_, ?_, ?_⟩
    · rintro g ⟨_, hg⟩
      exact hg
    · rintro g₁ ⟨h1, _⟩ g₂ ⟨h2, _⟩ he
      apply R.eG.injective
      funext PP'
      by_cases hq : PP' = P
      · rw [hq]
        have he' : ((R.eG g₁ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm =
            ((R.eG g₂ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm :=
          congrArg Units.val he
        exact Units.ext (Matrix.map_injective ρk.symm.injective he')
      · rw [h1 PP' hq, h2 PP' hq]
    · intro g₀ hg₀
      have hcomp : Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀) = g₀ := by
        ext j k
        simp
      refine ⟨R.eG.symm (Pi.mulSingle P (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀)), ⟨?_, ?_⟩, ?_⟩
      · intro PP' hq
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne hq]
      · rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
        exact hg₀
      · show Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG (R.eG.symm _) P) = g₀
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
  · intro g _
    rfl

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetValue

open GlobalTheory.SplitHecke

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_unit (u : (v.adicCompletionIntegers F)ˣ) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) u) = 1 := by
  by_contra hne
  exact (GlobalTheory.SplitUnif.mem_max v u).2 (lt_of_le_of_ne (u : v.adicCompletionIntegers F).2 hne) u.isUnit

theorem valued_irreducible {p : v.adicCompletionIntegers F} (hp : Irreducible p) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) p) = WithZero.exp (-1) := by
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  let p₀ : v.adicCompletionIntegers F := ⟨algebraMap F (Fv F v) t, GlobalTheory.SplitUnif.map_mem v _ t⟩
  have hp₀ : Valued.v (p₀ : Fv F v) = WithZero.exp (-1) := (hφ t).trans ht
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hp
    (GlobalTheory.SplitUnif.irreducible_of_valued v p₀ hp₀)
  have := congrArg (fun y : v.adicCompletionIntegers F => Valued.v (y : Fv F v)) hw
  change Valued.v ((p : Fv F v) * (w : v.adicCompletionIntegers F)) = Valued.v (p₀ : Fv F v) at this
  rw [map_mul, hp₀] at this
  have hw1 := valued_unit v w
  rw [← this]
  change _ = _ * Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) w)
  rw [hw1, mul_one]
  rfl

theorem card_residue_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) fun s => by
    rw [hφ, HeightOneSpectrum.intValuation_lt_one_iff_mem]

end Local

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chi_of_unit_gen (hπ : Chart e v π) {x d : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hd1 : (1 - e) * (d : AE D) = 1 - e) {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) {u : (Ov D v)ˣ}
    (h1 : π (d : AE D) = π (x : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u) : χ d = χ x := by
  have h3 : π ((x⁻¹ * d : (AE D)ˣ) : AE D) = algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [Units.val_mul, π.map_mul, h1, ← mul_assoc, ← π.map_mul, Units.inv_mul, π.map_one, one_mul]
  have h4 := hχ (x⁻¹ * d) ?_ ((hπ.2.2.2 _).2 ⟨u, h3.symm⟩) ((hπ.2.2.2 _).2 ⟨(u⁻¹ : (Ov D v)ˣ), ?_⟩)
  · rwa [χ.map_mul, χ.map_inv, inv_mul_eq_one, eq_comm] at h4
  · have h5 : (1 - e) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
      conv_lhs => rw [← hx1, mul_assoc, Units.mul_inv, mul_one]
    rw [Units.val_mul, ← mul_assoc, h5, hd1]
  · rw [map_units_inv, map_units_inv, h3]

end Chart

set_option maxHeartbeats 1000000 in

theorem det_modulus_chi : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  intro D V P e hP ϖ hϖ hϖ2 x hx k α hα k₁ hk₁ k₂ hk₂ z hz
  have he := hP.1
  obtain ⟨v, π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := GlobalTheory.T.splitChart_uniformiser_and_residueCard e P v π hP hπ ϖ hϖ hϖ2
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_splitFrame_selfDualLattice_completion e v π he hπ V
  have st := GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ V β hβ
  have hH : Hk (Ov D v) p k (rho V π β (k₁ * α * k₂)) := by
    rw [map_mul, map_mul]
    exact (GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ V β hβ (ϖ : D.host.E) p k α hpϖ hα).mul ((st _ hk₁.2).1 hk₁.1)
      ((st _ hk₂.2).1 hk₂.1)
  obtain ⟨u, hu⟩ := hH.2.2
  have hx1 : (1 - e) * (x : AE D) = 1 - e := by
    rw [hx]
    exact one_sub_mul_idem he.1 _
  have hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p := by
    rw [hx, π.map_add, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero, hpϖ]
  have hz1 : (1 - e) * (z : AE D) = 1 - e := by
    rw [hz]
    exact one_sub_mul_idem he.1 _
  have hz2 : π (z : AE D) = algebraMap (Ov D v) (Fv D.host.F v) (p ^ k * u) := by
    rw [rho_val, Matrix.det_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at hu
    rw [hz, π.map_add, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact hu
  refine ⟨?_, fun A _ χ hχ => ?_⟩
  · rw [GlobalTheory.SplitLinear.absFin_split D e v π he hπ z hz1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have e1 : ((Units.map π.toMonoidHom z : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (z : AE D) := rfl
    have e2 : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
      rw [← card_residue_eq, hq]
    have hv1 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) p) = WithZero.exp (-1) := valued_irreducible v hp
    have hv2 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) u) = 1 := valued_unit v u
    rw [e1, hz2, map_mul, map_mul, map_pow, map_pow, hv1, hv2, mul_one, e2,
      ← WithZero.exp_nsmul, WithZero.log_exp, nsmul_eq_mul, mul_neg_one, _root_.zpow_neg, zpow_natCast]
  · have h1 : π (z : AE D) = π ((x ^ k : (AE D)ˣ) : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u := by
      rw [hz2, Units.val_pow_eq_pow_val, π.map_pow, hx2, ← RingHom.map_pow, ← RingHom.map_mul]
    have h2 : ∀ j : ℕ, (1 - e) * ((x ^ j : (AE D)ˣ) : AE D) = 1 - e := fun j => by
      induction j with
      | zero => rw [pow_zero, Units.val_one, mul_one]
      | succ j ih => rw [pow_succ, Units.val_mul, ← mul_assoc, ih, hx1]
    exact (chi_of_unit_gen hπ (h2 k) hz1 hχ h1).trans (χ.map_pow x k)

end GlobalTheory.SplitDetValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModification
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem modStep_holds : ModStep := by
  intro l _ P AI T n _ _ K r ρ w x y hxy hR hF hS
  choose U hU hUe using hF
  obtain ⟨hfield, -, -, -, hval, hmul, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  haveI : Nontrivial P.R.BdR := ⟨hfield.exists_pair_ne⟩
  have hsum : ∀ (s : Finset n) (f : n → P.R.BdR), (∀ k ∈ s, f k ∈ Fil P 1) → ∑ k ∈ s, f k ∈ Fil P 1 := by
    intro s f hf
    unfold Fil at *
    exact sum_mem hf
  have h1 : (1 : P.R.BdR) ∉ Fil P 1 := by
    intro h
    obtain ⟨a, ha, ha'⟩ := hval 1 one_ne_zero
    exact ha' (by simpa using hmul a 1 1 1 ha h)
  have hcol : ∃ i, (U x.1 : Matrix n n P.R.BdR) i x.2 ∉ Fil P 1 := by
    by_contra hc
    push_neg at hc
    have hinv : (((U x.1)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * (U x.1 : Matrix n n P.R.BdR) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have he := congrFun (congrFun hinv x.2) x.2
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at he
    apply h1
    rw [← he]
    apply hsum
    intro k _
    simpa using hmul 0 1 _ _ ((hU x.1).2 x.2 k) (hc k)
  have heig : ∀ g : ↥(GK K), (matD P ρ (x.1 : ℕ) g).mulVec
      (fun i => P.actQdR (g : GQ l) ((U x.1 : Matrix n n P.R.BdR) i x.2)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w x.1 x.2 : ℚ_[l]ˣ) : ℚ_[l]) •
        (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) := by
    intro g
    funext i
    have h := congrFun (congrFun (hUe x.1 g) i) x.2
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
    simp only [Matrix.map_apply] at h
    rw [Matrix.mulVec, dotProduct, h, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hind := GlobalTheory.T.residue_indep_of_not_reducibleOverUnramified l P AI T n K r ρ (x.1 : ℕ) (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) (w x.1 x.2)
    hR hS (fun i => (hU x.1).1 i x.2) hcol heig
  obtain ⟨A, hA, hW⟩ := GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree r l P AI T n U x y hxy (fun m => hU m) hind
  exact GlobalTheory.T.exists_rep_of_frobeniusFixed_frame_change l P AI T n K r ρ w (fun m j => eps x y (m, j)) U A hR hUe hA hW

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEqStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l l' : List (WD h × ℕ)), (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) = sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' := by
  first | exact @GlobalTheory.WeilDeligne.SpUnique.perm_of_sumList_lpChar_lpSp_eq | exact GlobalTheory.WeilDeligne.SpUnique.perm_of_sumList_lpChar_lpSp_eq | (intros; apply GlobalTheory.WeilDeligne.SpUnique.perm_of_sumList_lpChar_lpSp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
section
noncomputable section

namespace GlobalTheory.SettingHypotheses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def FieldSelfDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∃ B : Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (X.O0 i)), B.det ≠ 0 ∧
    ∀ g g' : GE N, (∀ x, g' x = X.cc (g (X.cc.symm x))) →
      (Tdual i s g').map (algebraMap (X.O0 i) (FractionRing (X.O0 i))) * B =
        B * ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).map
          (algebraMap (X.O0 i) (FractionRing (X.O0 i)))

theorem setHyp_of_isTriple_of_galHodge (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀)
    (hG : GlobalTheory.TripleLocal.GalHodge D T) (h2 : Formalism.MainNotions.BlochKatoReduction.adm2 D) (h : GlobalTheory.Triple.IsTriple D)
    (Z : GlobalTheory.LamTie.LamDat D) (hZ : Z.Ok) (hL : GlobalTheory.LamTie.IsLamTie D.ntw Z)
    (hr : 100 ≤ D.R.r) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    ∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (bk0 D) i := fun i hi =>
  have hA := (GlobalTheory.TripleLocal.galois_hypotheses_of_isTriple S
    (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)) hG h2 h).2.2 i hi
  have hT := GlobalTheory.LamTie.sum_th_empty_ne_zero D D.nd D.ntw Z hZ
    (GlobalTheory.LamTieWeak.isLamTie0_of_isLamTie D D.nd D.ntw Z hL) i hi
  ⟨hA.1, fun s _ => (hA.2 s).1, fun s _ => (hA.2 s).2, fun lam => (hT lam).1, fun lam => (hT lam).2, hr, hg⟩

end GlobalTheory.SettingHypotheses
end
end

