import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLevel

open Classical in

theorem finsum_cosets_eq {G W : Type} [Group G] [AddCommMonoid W] (S K U : Subgroup G)
    (hU : ∀ κ ∈ S, (κ ∈ U ↔ κ ∈ K)) (F : G → W)
    (hF : ∀ x ∈ S, ∀ κ ∈ S, κ ∈ K → F (x * κ) = F x) :
    (∑ᶠ c : G ⧸ U, if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) =
      ∑ᶠ q : S ⧸ (K.subgroupOf S), F ((q.out : S) : G) := by

  have key : ∀ x y : G, x ∈ S → y ∈ S → (x⁻¹ * y ∈ U ↔ x⁻¹ * y ∈ K) := fun x y hx hy =>
    hU _ (S.mul_mem (S.inv_mem hx) hy)
  let ι : S ⧸ (K.subgroupOf S) → G ⧸ U := fun q => (((q.out : S) : G) : G ⧸ U)
  have hinj : Function.Injective ι := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have h1 := QuotientGroup.eq.1 h
    have h2 := (key _ _ (q.out).2 (q'.out).2).1 h1
    simpa using h2
  have hsupp : (Function.support fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) ⊆ Set.range ι := by
    intro c hc
    by_cases hc' : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S
    · obtain ⟨x, hxc, hxS⟩ := hc'
      refine ⟨((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S)), ?_⟩
      set q : S ⧸ (K.subgroupOf S) := ((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S))
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
      rw [Subgroup.mem_subgroupOf] at h1
      have h1' : ((q.out : S) : G)⁻¹ * x ∈ K := by simpa using h1
      rw [← hxc]
      exact QuotientGroup.eq.2 ((key _ _ (q.out).2 hxS).2 h1')
    · exact absurd (dif_neg hc') hc
  have hsum := finsum_mem_inter_support (fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) (Set.range ι)
  rw [Set.inter_eq_right.2 hsupp, finsum_mem_support, finsum_mem_range hinj] at hsum
  rw [hsum]
  refine finsum_congr fun q => ?_
  have hc : ∃ x : G, (x : G ⧸ U) = ι q ∧ x ∈ S := ⟨((q.out : S) : G), rfl, (q.out).2⟩
  rw [dif_pos hc]
  obtain ⟨h1, h2⟩ := hc.choose_spec
  have hm : ((q.out : S) : G)⁻¹ * hc.choose ∈ K :=
    (key _ _ (q.out).2 h2).1 (QuotientGroup.eq.1 h1.symm)
  have e : hc.choose = ((q.out : S) : G) * (((q.out : S) : G)⁻¹ * hc.choose) := by group
  rw [e, hF _ (q.out).2 _ (S.mul_mem (S.inv_mem (q.out).2) h2) hm]

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem heckeFunI_level_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → ∀ (U U' : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ, TrivOutside {v} κ → (κ ∈ U' ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), Formalism.UG.IsBiInv (Formalism.UG.KU Dv.σw n) h → ∀ φ : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → heckeFunI L n U Dv h φ = heckeFunI L n U' Dv h φ := by
  intro L _ _ _ n v w Dv hKU U U' hU hU' W _ _ h hbi φ hφ
  funext g

  let F : GAf L n → W := fun x => Dv.hval h (Dv.loc x) • φ (g * x)
  have hF : ∀ x ∈ GlobalTheory.InertSph.Gv L n v, ∀ κ ∈ GlobalTheory.InertSph.Gv L n v, κ ∈ Umax L n → F (x * κ) = F x := by
    intro x _ κ hκS hκU
    obtain ⟨hκ, hk⟩ := hKU κ hκU hκS
    have hloc : Dv.loc (x * κ) = Dv.loc x * Dv.loc κ := (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x κ
    have hφκ : φ (g * x * κ) = φ (g * x) := congrFun (hφ κ hκU hκS) (g * x)
    have hval : Dv.hval h (Dv.loc x * Dv.loc κ) = Dv.hval h (Dv.loc x) := by
      unfold InertDatum.hval
      by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
      · have hyk : Dv.loc x * Dv.loc κ ∈ Formalism.UG.GU Dv.σw n := (Formalism.UG.GU Dv.σw n).mul_mem hy hκ
        rw [dif_pos hyk, dif_pos hy]
        have e := hbi 1 ⟨⟨Dv.loc κ, hκ⟩, hk⟩ ⟨Dv.loc x, hy⟩
        simp only [OneMemClass.coe_one, one_mul] at e
        exact e
      · have hyk : Dv.loc x * Dv.loc κ ∉ Formalism.UG.GU Dv.σw n := fun hm => hy (by
          simpa using (Formalism.UG.GU Dv.σw n).mul_mem hm ((Formalism.UG.GU Dv.σw n).inv_mem hκ))
        rw [dif_neg hyk, dif_neg hy]
    show Dv.hval h (Dv.loc (x * κ)) • φ (g * (x * κ)) = Dv.hval h (Dv.loc x) • φ (g * x)
    rw [hloc, hval, ← mul_assoc, hφκ]
  have e1 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U (fun κ hκ => hU κ hκ) F hF
  have e2 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U' (fun κ hκ => hU' κ hκ) F hF
  exact e1.trans e2.symm

end GlobalTheory.InertLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocal

open Formalism.IndefR.principalLevelFrame in

theorem finTyp_fixed_finiteDimensional : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (X : RowMod D rep j) (σ : D.what₂.FT), Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := by
  intro D rep j X σ hne N hN
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : (rep σ).S →ₗ[ℂ] X.A,
      (IsEqvA X.ρ (rep σ) Φ ∧ LinearMap.range Φ ≤ X.C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hne
    unfold Formalism.IndefR.principalLevelFrame.isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E D.R.r → ℂ) := (LinearMap.ker Φ).map (rep σ).S.subtype
    have hS'le : S' ≤ (rep σ).S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E D.R.r h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E D.R.r h k, (rep σ).stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases (rep σ).irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E D.R.r → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E D.R.r → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ X.C ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → X.ρ κ x = x} with hT
  have := X.adm N hN
  have hFS : F ≤ (rep σ).S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : (rep σ).S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : (rep σ).S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : (rep σ).S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

section Asm
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have h1 := hx v hv
  have h2 := hy v hv
  show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
  rw [Units.val_mul, Matrix.map_mul, h1, h2, mul_one]

theorem isLocS_of_irr (π : NG.FinTyp L n) (s : SplitPlace L) (W : Submodule ℂ (GAf L n → ℂ)) (hWS : W ≤ π.S)
    (hW0 : W ≠ ⊥) (hst : ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W)
    (hirr : ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ τ, IsLocS π.S s τ := by
  first
  | exact @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | (apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component ..)

end Asm
end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

theorem finTyp_exists_isLocS : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (_ : RowMod D rep j) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ, IsLocS (rep σ).S s τ := by
  intro D rep j X σ hσ s
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos
    X.stab X.inv (rep σ) hne
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r (rep σ) B' hlin hherm hpos hinv (finTyp_fixed_finiteDimensional D rep j X σ hne) s
  exact isLocS_of_irr (rep σ) s W hWS hW0 hst hirr

end GlobalTheory.RowLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalAboveL
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CaraianiAboveL

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.CaraianiLocalGlobal →
    GlobalTheory.Published.LocalGlobalAboveL := by
  intro hF hL hC E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh r wt HT hG P AI hT w A h O _ _ _ Bw hj σ hσ rc hrc
  obtain ⟨R, hRc, hRs, hRaway, hRabove⟩ := hC E Ω l ι a ha π hc hcoh
  have htr : ∀ (w' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w'.asIdeal → ∀ (A' : ValuationSubring Ω)
      (h' : IsPlaceOver A' w') (τ : Weil h'), (R (τ : G E Ω)).val.trace = (r (τ : G E Ω)).val.trace := by
    intro w' hl A' h' τ
    obtain ⟨rc', hrc', -⟩ := hL.1 E Ω A' w' h'
    obtain ⟨σ', hσ', -⟩ := LocEx.exists_isLocComp hF E a π w'
    exact GlobalTheory.T.weil_trace_eq_of_same_wd E Ω l ι a R r w' A' h' (rc' (algNorm σ')) hl (hRaway w' hl A' h' rc' hrc' σ' hσ')
      (hG.away w' hl A' h' rc' hrc' σ' hσ') τ
  obtain ⟨p, hp⟩ := GlobalTheory.T.semisimple_conj_of_trace_equal E Ω l a R r hRc hG.cont hRs hG.ss htr
  obtain ⟨hpst, hR⟩ := hRabove P AI hT w A h O Bw hj
  have hwd := GlobalTheory.T.fontaineParameter_invariant_under_conjugation E Ω l ι a P AI hT w A h O Bw hj (R.comp (Dec (F := E) A).subtype)
    (r.comp (Dec (F := E) A).subtype) p (fun g => hp g) hpst
  rw [hwd.2]
  exact hR σ hσ rc hrc

end GlobalTheory.CaraianiAboveL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalCompatibility
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem GlobalTheory.StringRepresentationDecomposition.local_global_compat_of_adm : ∀ D : D7, SumRepresentations.AdmA D → LGC D := by
  intro D hA i r hr w hw x
  obtain ⟨ht, _, h1, h2, _, _, h5⟩ := hA
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, hl⟩ := GlobalTheory.GalIsoBC.galRep_isobaric D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x P Pa hP hPa ρ hc hss
    (fun w _ => hwd w)
  refine ⟨P, hP, ?_⟩
  have hsp := D.nd.SQ_split i w hw
  rw [← hPa.2.2.2.1 w hsp, ← hwd w]
  have hok : SumRepresentations.At.WDok D.nd D.naut i ρ w := by
    by_cases hwl : w ∈ placesOver D.host.E (D.nd.l i)
    · exact Or.inr (hl w hwl).1
    · exact Or.inl hwl
  exact ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_systems_lower_bounds_second_real_place : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  first | exact @GlobalTheory.TwU.SiteSys.sysTw_sites | exact GlobalTheory.TwU.SiteSys.sysTw_sites | (intros; apply GlobalTheory.TwU.SiteSys.sysTw_sites <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegrality
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem normalisedFamily_standardBases_integrality : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hA hO hCS
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hCD, hH⟩ := hA
  obtain ⟨om, oms, ζ, hBD⟩ := GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData p g2 g3 s2 ε σ F hCD (nP D p) hO.even
  refine ⟨c, beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ, hc,
    ⟨σ, F, cob F (phFF p g2 g3 s2 ε), om, oms, ζ, hBD, rfl⟩, ?_⟩
  intro N N' L L' P P' hAdm hP hP' G hG R hR
  obtain ⟨r, b, hb, ho, hint⟩ := hH N N' L L' hAdm
  obtain ⟨f, f', hf, heq⟩ := GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst D p lam σ hCD.2.2.2.2.2.1 hO hCS om oms hBD.2.2.2.2.1 hBD.2.2.2.2.2.1
    R hR N N' L L' P P' hAdm hP hP' r b hb ho
  exact GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt D p g2 g3 s2 ε σ F hCD hO om oms ζ hBD R hR N N' r f f' hf (thOrth D lam c b G) (hint G hG) c
    (stdSer D lam (fun _ => 1) P P' G) (heq c G)

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartitionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicProduct_equiv_product_of_partition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)) (r t : ℕ) (e : (Σ a, Fin (d a)) ≃ Fin (r + t)) (e₁ : (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) ≃ Fin r) (e₂ : (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) ≃ Fin t), (∀ a b, a ∉ S → b ∈ S → ∀ (n : Type) [Fintype n] [DecidableEq n] (f : (Σ i : Fin 2, Fin (d (![a, b] i))) ≃ n) (f' : (Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ n), Nonempty ((multiProd f fun i => (σ (![a, b] i)).π).Equiv (multiProd f' fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π))) → Nonempty ((multiProd e fun a => (σ a).π).Equiv (prod₂ (multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π) (multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π))) := by
  first | exact @GlobalTheory.ProdReorder.reorder_split | exact GlobalTheory.ProdReorder.reorder_split | (intros; apply GlobalTheory.ProdReorder.reorder_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameChara
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockSupp

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) ∧ t ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro hBZ hGL _ hDZ k _ _ _ _ r t χ π v hχs hχt hv hbv
  obtain ⟨s, d, σ, hsupp⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL k (r + t) π
  obtain ⟨e, x, hx, hxe⟩ := GlobalTheory.T.tame_block_vector_jacquet_nonzero hDZ k r t χ π v hχt hv hbv
  refine ⟨s, d, σ, hsupp, ?_⟩
  have h := GlobalTheory.T.card_le_unramifiedTwists_cuspidalSupport_jacquet hBZ hGL k (r + t) s (t + 1) χ π d σ _ e (Finset.univ.map (Fin.succEmb t)) x hχs hsupp
    (by intro j hj; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; rfl) hx
    (by intro j hj g hg; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; exact hxe i g hg)
  simpa using h

end GlobalTheory.BlockSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeterssonFormProportionalClassSumAllLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ChainE

variable {D : D7}

theorem mult_level {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (U : MMap M) (hU : U ∈ Mult θ M J χ) (v : M.Vec) : ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy, mul_add]
  | smul a x _ hx => simp only [MultilinearMap.smul_apply, Pi.smul_apply, hx, smul_eq_mul, mul_left_comm]

theorem natCast_pow_notMem (P : Pl D.host.E) {n : ℕ} (h : ((n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (c : ℕ) :
    ((n ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
  h (P.isPrime.mem_of_pow_mem c (by rwa [Nat.cast_pow] at h'))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (H : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (Φ : GA D V → ℂ)
    (h : ∀ g0 : G0 L.Pg L.r, actG0 V β L g0 (H Φ) = H (actG0 V β L g0 Φ)) :
    gaL V β L eG c (H Φ) = H (gaL V β L eG c Φ) := by
  unfold gaL
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg (c g • ·) (h (eG g))

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnFrom_hk (t : T) (P : Pl D.host.E) (cs : ℕ → List ℤ →₀ ℂ)
    (hs : ∀ k, k + 1 < D.R.m → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P (cs (k + 1)) (U.1 v)) →
      ∀ v, (R.ioY t k U').1 v = hk _ P (cs k) ((R.ioY t k U).1 v))
    (n : ℕ) (hn : n < D.R.m) (U U' : R.CC t n) (hU : ∀ v, U'.1 v = hk _ P (cs n) (U.1 v)) :
    ∀ v, (Lift.dnFrom (R.CC t) (R.ioY t) n U').1 v = hk _ P (cs 0) ((Lift.dnFrom (R.CC t) (R.ioY t) n U).1 v) := by
  induction n with
  | zero => exact hU
  | succ k ih => exact ih (by omega) (R.ioY t k U) (R.ioY t k U') (hs k hn U U' hU)

noncomputable def liftCC (t : T) (y : (R.HX t).H) : R.CC t 0 :=
  Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))

theorem thDn_eq (t : T) (y : (R.HX t).H) : R.thDn t y = (liftCC t y).1 := rfl

theorem e_Th (hT : R.chain_Th) (t : T) (x : (R.HX t).H) (v : (R.MY 0).Vec) : R.HE.e (R.Th t x) v =
    R.e0 ((liftCC t x).1 (PiTensorProduct.tprod ℂ v)) := by
  rw [hT t x, postOn_apply, thDn_eq t x]
  rfl

theorem compositeLift_relation_passes_to_rows (F : Face D A) (hl : R.toLevCh.Is A.μ0) (t : T) (P : Pl D.host.E) (hP : Good R t P) (c : List ℤ →₀ ℂ) (U : R.CC t 0)
    (v : (R.MY 0).Vec) :
    R.e0 (hk _ P c (U.1 (PiTensorProduct.tprod ℂ v))) = hk _ P c (R.e0 (U.1 (PiTensorProduct.tprod ℂ v))) := by
  obtain ⟨n, hn⟩ := hl.βY 0 (by have := D.R.two_le_m; omega)
  have hN := natCast_pow_notMem P ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hl).2.1 t P hP).1 n
  have h1 := (GlobalTheory.T.level_operators_at_prime_off_level_datum _ _ _ _ (R.datYt t 0 R.triv) hn P hN hP).1
  have h2 := (GlobalTheory.T.level_operators_at_prime_off_level_datum _ _ _ _ (R.dat0 R.triv) hn P hN fun PP h =>
    hP PP (Or.inl (h.resolve_right (Finset.notMem_empty PP)))).2.2.2.1
  have h3 := mult_level _ _ _ _ _ ((mem_multT R.θ (R.MY 0) _ _ _).1 U.2) v
  refine gaL_comm _ _ _ _ _ _ _ fun g0 => h2 c g0 _ fun k hk h => ?_
  have h4 := h3 k (h1 k hk).1 h
  rw [(h1 k hk).2, one_mul] at h4
  exact h4

theorem e_Th_hk (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hT : R.chain_Th) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (c : List ℤ →₀ ℂ) (y y' : (R.HX t).H) (h : ∀ v, (liftCC t y').1 v = hk _ P c ((liftCC t y).1 v)) :
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e (R.Th t y)) := by
  refine MultilinearMap.ext fun v => ?_
  exact ((e_Th hT t y' v).trans ((congrArg R.e0 (h _)).trans (compositeLift_relation_passes_to_rows F hl t P hP c (liftCC t y) v))).trans
    ((postOn_apply _ _ _ v).trans (congrArg (hk (Yc D 0) P c) (e_Th hT t y v))).symm

end Chain

theorem matchE_of_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → FixAll R t P → ∀ (cX : List ℤ →₀ ℂ) (cs : ℕ → List ℤ →₀ ℂ), Match R.ψ (R.ωX t) P (cs (D.R.m - 1)) (dualC cX) → (∀ k, k + 1 < D.R.m → Match R.ψ (R.ωY t k) P (cs k) (dualC (cs (k + 1)))) → MatchE R t P cX (cs 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P hP hF cX cs hX hY y y' hy
  refine e_Th_hk F hC.lev hC.chain.Th t P hP (cs 0) y y' ?_
  exact dnFrom_hk t P cs (fun k hk => GlobalTheory.T.chainInnerStep_intertwines_matchedHecke R F hI hC hS t P k hP hk (hF.1 k hk) _ _ (hY k hk))
    (D.R.m - 1) (by have := D.R.two_le_m; omega) _ _ (GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke R F hC hS t P hP hF.2.1 _ _ hX y y' hy)

end GlobalTheory.Hk3.ChainE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAdmissibleStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusionG6_of_admissible : ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @GlobalTheory.ClosingSixth.conclusionG6_of_adm | exact GlobalTheory.ClosingSixth.conclusionG6_of_adm | (intros; apply GlobalTheory.ClosingSixth.conclusionG6_of_adm <;> assumption)
end

