import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PosOfMulPosOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle0001
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CobOfCoord
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0011
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0008
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.MonodromyFreeOfEigenvalueRatio
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0072
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0071
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.EndoscopicGroupCriteria.UnitaryUp3OfUpAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0003

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConj
section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3

private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]

private theorem charpoly_conj {H K K' : Type} [Group H] [Field K] [Field K'] (f : K →+* K') {r r' : H →* M4 K}
    (h : IsConj4 r r') (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  obtain ⟨u, hu⟩ := h
  show ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, hu, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end SlopeTestRemainingChoices
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.GalUnitaryW
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Gu

open UpperTheory.GalN.V
open private ev_notMem from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GalUnitary

def UpperTheory.GalN.V.GalUnitaryW : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      ∃ (r : G E Ω →* GL (Fin n) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ), Continuous r ∧ IsSSRep r ∧
        (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU σ w →
          ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, r s = 1) ∧
        HasHT r HT ∧
        (∀ (τ : E →+* Qbar l) lam, HasWeightAt σ (ι.toRingHom.comp τ) lam →
          (HT τ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z) ∧
        (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlob ι r w τ) ∧
        (∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P) ∧
        (IsIrr r → ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧
          ∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧
        (IsIrr r → ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
          (IsUnramU σ w ∨ IsSplitAt w ∧ ∃ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
            IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ (rc (algNorm τ)).mono0) → UnlinkAt r w A)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IndLoc0
section
open UpperTheory.GalN.V

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem near {K : Type} [NormedField K] [IsUltrametricDist K] (d x y z : K) (hd : ‖d - 1‖ < 1) (hx : ‖x - y‖ < 1)
    (hy : ‖y‖ = 1) (hz : ‖z - y‖ < 1) : ‖d * x - z‖ < 1 := by
  have h1 : ‖x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hx.le hy.le)
  have h2 : ‖(d - 1) * x‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h1) hd
  have h3 : d * x - z = (d - 1) * x + ((x - y) + (y - z)) := by ring
  rw [h3]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 ?_)
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx ?_)
  rwa [norm_sub_rev]

theorem UpperTheory.GalN.V.indLoc0 :
    AllInd fun {Ω} _ _ _ {l} _ _ _ T _ R δ => ∃ n, LocOk T ⟨twF T R δ, n⟩ ∧ ∃ (m : Fin 4 → ℤ) (b : ℤ) (N : ℕ),
  (∀ i : Fin 3, m i.succ + 2 ≤ m i.castSucc) ∧ Wts0 T (fun i => 2 * m i + b) ⟨twF T R δ, n⟩ ∧ 0 < N ∧
  ∀ g, (δ g ^ 2 * cycBar T.F Ω l g ^ (-b)) ^ N = 1 := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  obtain ⟨m, hm, hF⟩ := UpperTheory.induced_flag_condition Ω l c D T k₀ φ ι k t r α β R δ H
  obtain ⟨b, N, U, hN, hδ, hU, hI⟩ := UpperTheory.induced_deletion_condition Ω l c D T k₀ φ ι k t r α β R δ H
  choose n hn using fun v : T.ι => hF (T.pl v) (T.ovl v)
  have key : ∀ v s, adj (n v) * twF T R δ s * n v = (δ s : Qbar l) • (adj (n v) * (R (resQ T.F s) : M4 (Qbar l)) * n v) := by
    intro v s
    have : twF T R δ s = (δ s : Qbar l) • (R (resQ T.F s) : M4 (Qbar l)) := tw_val (R.comp (resQ T.F)) δ s
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have key' : ∀ v s i, PD.ψ (⟨twF T R δ, n⟩ : PD T.ι (G T.F Ω) (Qbar l)) v i s =
      (δ s : Qbar l) * (adj (n v) * (R (resQ T.F s) : M4 (Qbar l)) * n v) i i := by
    intro v s i
    show (adj (n v) * twF T R δ s * n v) i i = _
    rw [key, Matrix.smul_apply, smul_eq_mul]
  have ined : ∀ (A : ValuationSubring Ω) (s : G T.F Ω), s ∈ Ine (F := T.F) A → s ∈ Dec (F := T.F) A := fun A s hs => hs.1
  refine ⟨n, ⟨fun v => (hn v).1, ?_, ?_, ?_⟩, m, b, N, hm, ⟨U, hU, ?_⟩, hN, hδ⟩
  · intro v s hs i j hij
    show (adj (n v) * twF T R δ s * n v) i j = 0
    rw [key, Matrix.smul_apply, ((hn v).2 s hs).1 i j hij, smul_zero]
  · intro v s hs i
    obtain ⟨h1, h2⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l H.hyp.good.l_odd (T.pl v) (T.ovl v) s hs
    have h3 : cycBar T.F Ω l s = 1 := by
      simp [cycBar, h2]
    rw [key', (((hn v).2 s (ined _ _ h1)).2 i).2 h1, (hI _ (T.ovl v) s h1).2 h2, h3]
    simp
  · intro v s hs i
    rw [key']
    have hk : resQ T.F s ∈ k₀.fixingSubgroup := H.hyp.spl _ (T.ovl v) hs
    refine near _ _ _ _ (H.δ_one s) (((hn v).2 s hs).2 i).1 ?_ (H.chars.inn s hk i)
    fin_cases i
    · exact H.chars.unit D.ξ _
    · simp
    · exact H.chars.unit D.ξ _
    · simp
  · intro v i s hs
    rw [key', (((hn v).2 s (ined _ _ hs.2)).2 i).2 hs.2, ← Units.val_mul, ← Units.val_pow_eq_pow_val, mul_pow,
      (hI _ (T.ovl v) s hs.2).1 hs.1, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 2
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
open private ss_conj from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdMain
open private isIrr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible
open private charpoly_conj_gl from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem Wit.iso' [IsCMField F] (e : RepIso r r') (hU : Wit ι r) : Wit ι r' := by
  intro w hw A hA hfin
  obtain ⟨g, hg⟩ := e
  have hfin' : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (hfin.image (fun x => g⁻¹ * x * g)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨r' s, ⟨s, hs, rfl⟩, ?_⟩
    simp only [hg s]
    group
  obtain ⟨s, j, hj, hF, h⟩ := hU w hw A hA hfin'
  refine ⟨s, j, hj, hF, fun α β hα hβ k hk => ?_⟩
  rw [hg s, charpoly_conj_gl] at hα hβ
  exact h α β hα hβ k hk

theorem attC_iso [IsTotallyComplex F] {π : CuspSub F n} (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π :=
  ⟨ss_conj h.choose h.choose_spec H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : IsAutCsdN ι r) : IsAutCsdN ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).iso' h⟩

def AutPN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := AutPol ι r ∧ Wit ι r
end

def AutQIsoN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → IsAutQN ι r' → IsAutQN ι r

def NewformAut0 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutomorphicOverImagQuad ι W

def Up30 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 3) (Qbar l)),
    IsAutR ι r → IsAutomorphicOverImagQuad ι r

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RwOfOrdForm
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
open private rep_retr iwahori_level_zero_eq from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.rw_of_ordForm (PH : HypothesesH) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  have P := PH.toClassicalTheorems
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  refine hG.ratio w hl A h rc hrc σ hσ ?_
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    obtain ⟨B, hB⟩ := (satLoc P F 2 w σ).1 ⟨T v, hTv, fun u hu => by rw [← hT, hf u (iwahori_level_zero_eq w ▸ hu)]⟩
    exact WD.unr_mono0 _ (UpperTheory.GalN.V.unr_algNorm hrc σ B hB)
  · have hA : ¬ A.valuation (l : Ω) < 1 := fun e => hl (((UpperTheory.V.Base.places F Ω l A).2.2.1 w h).1 e)
    obtain ⟨s₀, hs₀, h0⟩ := SetLike.not_le_iff_exists.1 fun e => ((H.ram w A h).1 e).elim hc hl
    obtain ⟨g, hg⟩ := UpperTheory.V.Sd.ordAway_n PH F Ω l ι ξ s c m a π r H A hA
    refine UpperTheory.GalN.V.L.monosep F Ω A w h _ (ineIncl h ⟨s₀, hs₀⟩) (deg_ineIncl _) ?_
    have k : UpperTheory.GalN.V.WDN ι r (rc (algNorm σ)) :=
      .of_aw hl H.cont ⟨(hG.away w hl A h rc hrc σ hσ).pol, (hG.away w hl A h rc hrc σ hσ).n0⟩
    have e : (r s₀ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C 1) * (X - C (ξ s₀ : Qbar l)) := by
      rw [← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, hg s₀ hs₀,
        Matrix.charpoly_diagonal, Fin.prod_univ_two]
      rfl
    rw [WD.eig, ← k.charpoly hl, coe_ineIncl, e]
    have h1 : ι (ξ s₀ : Qbar l) ≠ 1 := fun e' => h0 (Units.ext (ι.injective (by simpa using e')))
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, map_X, map_C, map_C]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
    simpa using h1.symm
end
end

