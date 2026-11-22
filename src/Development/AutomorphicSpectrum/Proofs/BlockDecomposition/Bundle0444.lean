import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0373
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpen
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HBBump

theorem exists_bump : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G),
    IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) →
    ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧
      ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  intro G Z _ _ _ _ _ H ρ B hBo hBc z hz
  classical

  have hwell : ∀ (h h' : H) (β β' : G), β ∈ B → β' ∈ B → (h : G) * β = (h' : G) * β' →
      ρ h z = ρ h' z := by
    intro h h' β β' hβ hβ' e
    have ha : ((h'⁻¹ * h : H) : G) ∈ B := by
      have : ((h'⁻¹ * h : H) : G) = β' * β⁻¹ := by
        push_cast
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
        group
      rw [this]
      exact B.mul_mem hβ' (B.inv_mem hβ)
    have h1 := hz _ ha
    have h2 : h = h' * (h'⁻¹ * h) := by group
    rw [h2, map_mul, Module.End.mul_apply, h1]
  let P : G → Prop := fun p => ∃ h : H, ∃ β ∈ B, p = (h : G) * β
  let f : G → Z := fun p => if hp : P p then ρ hp.choose z else 0
  have hval : ∀ (h : H) (β : G), β ∈ B → f ((h : G) * β) = ρ h z := by
    intro h β hβ
    have hp : P ((h : G) * β) := ⟨h, β, hβ, rfl⟩
    obtain ⟨β', hβ', e⟩ := hp.choose_spec
    simp only [f, dif_pos hp]
    exact hwell _ _ _ _ hβ' hβ e.symm
  have hzero : ∀ p, ¬ P p → f p = 0 := fun p hp => by simp only [f, dif_neg hp]
  have hleft : ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g) := by
    intro h g
    by_cases hg : P g
    · obtain ⟨h', β, hβ, rfl⟩ := hg
      have : (h : G) * ((h' : G) * β) = ((h * h' : H) : G) * β := by push_cast; group
      rw [this, hval _ _ hβ, hval _ _ hβ, map_mul, Module.End.mul_apply]
    · have hn : ¬ P ((h : G) * g) := by
        rintro ⟨h', β, hβ, e⟩
        refine hg ⟨h⁻¹ * h', β, hβ, ?_⟩
        push_cast
        rw [mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hg, map_zero]
  have hright : ∀ (p : G), ∀ x ∈ B, f (p * x) = f p := by
    intro p x hx
    by_cases hp : P p
    · obtain ⟨h, β, hβ, rfl⟩ := hp
      rw [mul_assoc, hval _ _ (B.mul_mem hβ hx), hval _ _ hβ]
    · have hn : ¬ P (p * x) := by
        rintro ⟨h, β, hβ, e⟩
        refine hp ⟨h, β * x⁻¹, B.mul_mem hβ (B.inv_mem hx), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hp]
  let F : indSpace H ρ := ⟨f, hleft⟩
  have hsm : F ∈ smoothPart (ind H ρ) := by
    let T : Subgroup G :=
      { carrier := {g | ind H ρ g F = F}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hBT : (B : Set G) ⊆ T := by
      intro x hx
      show ind H ρ x F = F
      apply Subtype.ext
      funext p
      exact hright p x hx
    exact T.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset (hBo.mem_nhds B.one_mem) hBT)
  refine ⟨⟨⟨F, hsm⟩, ⟨(B : Set G), hBc, ?_⟩⟩, hval, hzero⟩
  intro g hg
  by_contra hc
  refine hg (hzero g ?_)
  rintro ⟨h, β, hβ, e⟩
  exact hc ⟨h, h.2, β, hβ, e⟩

end GlobalTheory.CompanionTheory.HBBump
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.UnitAct

section Ring

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F (Om l)] [ValuativeExtension F (Om l)]

theorem valuation_le_one_iff (x : F) :
    valuation F x ≤ 1 ↔ ‖algebraMap F (Om l) x‖ ≤ 1 := by
  rw [← map_one (valuation F), ← (valuation F).vle_iff_le, ← ValuativeExtension.vle_iff_vle (B := Om l),
    GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, map_one, norm_one]

theorem exists_ringEquiv (hR : Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l))) :
    ∃ ρ : 𝒪[F] ≃+* ↥(OL K), ∀ a : 𝒪[F],
      (((ρ a : ↥(OL K)) : ↥K.1) : Om l) = algebraMap F (Om l) (a : F) := by
  have hmem : ∀ a : 𝒪[F], algebraMap F (Om l) (a : F) ∈ K.1 := fun a => by
    have h : algebraMap F (Om l) (a : F) ∈ (K.1 : Set (Om l)) := hR ▸ ⟨_, rfl⟩
    exact h
  have hO : ∀ a : 𝒪[F], (⟨_, hmem a⟩ : ↥K.1) ∈ OL K := fun a =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr ((valuation_le_one_iff (a : F)).mp a.2)
  let f : 𝒪[F] →+* ↥(OL K) :=
    { toFun := fun a => ⟨⟨_, hmem a⟩, hO a⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun a b => Subtype.ext (Subtype.ext (by simp)) }
  have hinj : Function.Injective f := fun a b hab => by
    have h : algebraMap F (Om l) (a : F) = algebraMap F (Om l) (b : F) :=
      congrArg (fun c : ↥(OL K) => ((c : ↥K.1) : Om l)) hab
    exact Subtype.ext ((algebraMap F (Om l)).injective h)
  have hsurj : Function.Surjective f := fun b => by
    have hb : ((b : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) := (b : ↥K.1).2
    rw [← hR] at hb
    obtain ⟨y, hy⟩ := hb
    have hn : ‖algebraMap F (Om l) y‖ ≤ 1 := by
      rw [hy]
      exact (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mp b.2
    exact ⟨⟨y, (valuation_le_one_iff y).mpr hn⟩, Subtype.ext (Subtype.ext hy)⟩
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => rfl⟩

theorem card_quot (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    Nat.card (↥(OL K) ⧸ Ideal.span {ρ π}) = Nat.card 𝓀[F] := by
  have e1 : (𝒪[F] ⧸ Ideal.span {π}) ≃ (↥(OL K) ⧸ Ideal.span {ρ π}) :=
    (Ideal.quotientEquiv (Ideal.span {π}) (Ideal.span {ρ π}) ρ
      (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv
  have e2 : 𝓀[F] ≃ (𝒪[F] ⧸ Ideal.span {π}) :=
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv
  exact Nat.card_congr (e2.trans e1).symm

theorem map_ltPoly (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F]) = ltSeries (ρ π) := by
  rw [ltSeries, card_quot ρ hπ, ltPoly]
  simp

end Ring

theorem main : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  intro l _ K χ hχ F _ _ _ _ _ _ _ hR
  obtain ⟨πK, z, hπK, h0, h1, hs, hch⟩ := hχ
  obtain ⟨ρ, hρ⟩ := exists_ringEquiv (K := K) (F := F) hR
  have hρπ : ρ (ρ.symm πK) = πK := ρ.apply_symm_apply πK
  obtain ⟨π, hπdef⟩ : ∃ π : 𝒪[F], π = ρ.symm πK := ⟨_, rfl⟩
  rw [← hπdef] at hρπ
  have hπ : Irreducible π := hπdef ▸ (MulEquiv.irreducible_iff ρ.symm).mpr hπK
  have hf := isLubinTateSeries_ltPoly π
  have hcard : Nat.card (↥(OL K) ⧸ Ideal.span {πK}) = Nat.card 𝓀[F] := by
    have h := card_quot ρ hπ
    rwa [hρπ] at h
  have hcoe : ((πK : ↥K.1) : Om l) = algebraMap F (Om l) (π : F) := by
    rw [← hρ π, hρπ]
  have hs' : ∀ n, algebraMap F (Om l) (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n :=
    fun n => by
      rw [← hcoe, ← hcard, add_comm]
      exact hs n
  have hv : ∀ n, valuation (Om l) (z n) < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => exact CharEx.valuation_lt_one_of_eq hπ ih (hs' n)
  let Z : ℕ → IdealPoint (Om l) (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hv n)
  have heval : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) →
      ∀ n, (a • Z n).val = (h : GQ l) (z n) := by
    intro a h ha n
    let Φ : PowerSeries 𝒪[F] := (lubinTateHom hπ hf hf a).toPowerSeries
    let ψ : PowerSeries ↥(OL K) := PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) Φ
    have hΦ0 : PowerSeries.constantCoeff Φ = 0 := (lubinTateHom hπ hf hf a).constantCoeff_eq_zero'
    have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, map_zero]
    have hψ1 : ((PowerSeries.coeff 1 ψ : ↥(OL K)) : ↥K.1) = ((χ h : (↥K.1)ˣ) : ↥K.1) := by
      rw [PowerSeries.coeff_map, coeff_one_lubinTateHom]
      exact ha
    have hF0 : PowerSeries.constantCoeff (ltPoly π : PowerSeries 𝒪[F]) = 0 :=
      hf.constantCoeff_eq_zero
    have hsub : PowerSeries.subst ψ (ltSeries πK) = PowerSeries.subst (ltSeries πK) ψ := by
      have h2 := congrArg (MvPowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)))
        (subst_lubinTateHom hπ hf hf a)
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hΦ0),
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)] at h2
      change PowerSeries.subst ψ (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) =
        PowerSeries.subst (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) ψ at h2
      rwa [map_ltPoly ρ hπ, hρπ] at h2
    have hsum := hch h ψ hψ0 hψ1 hsub n
    have hsum2 := CharEx.hasSum_coeff_mul_pow (K := F) Φ (hv n)
    rw [lubinTate_smul_val]
    refine hsum2.unique ?_
    convert hsum using 2 with k
    simp only [ψ, PowerSeries.coeff_map]
    rw [← hρ]
    rfl
  have hZ0 : Z 0 = 0 := IdealPoint.ext h0
  have hZ1 : Z 1 ≠ 0 := fun h => h1 (congrArg IdealPoint.val h)
  have hstep : ∀ n, π • Z (n + 1) = Z n := fun n => IdealPoint.ext (by
    rw [lubinTate_uniformizer_smul_val]
    change psEval ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) (fun _ => z (n + 1)) = z n
    rw [psEval_polynomial, aeval_ltPoly]
    exact hs' n)
  have hpow : ∀ n, π ^ n • Z (n + 1) = Z 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hstep, ih]
  have hunit : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) → IsUnit a := by
    intro a h ha
    by_contra hnu
    have hm := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨b, rfl⟩ := hm
    have h2 : (b * π) • Z 1 = 0 := by rw [mul_smul, hstep, hZ0, smul_zero]
    have h3 := heval _ h ha 1
    rw [h2] at h3
    exact h1 ((map_eq_zero_iff _ (h : GQ l).injective).mp h3.symm)
  refine ⟨π, hπ, fun g g' hg => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[F]ˣ,
      algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) := by
    have hy : (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) :=
      ((χ g' : (↥K.1)ˣ) : ↥K.1).2
    rw [← hR] at hy
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (χ g').ne_zero (Subtype.ext hy.symm)
    rcases le_total (valuation F y) 1 with hle | hle
    · obtain ⟨w, hw⟩ := hunit ⟨y, hle⟩ g' (Subtype.ext (by rw [hρ]; exact hy))
      exact ⟨w, by rw [hw]; exact hy⟩
    · have hle' : valuation F y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hle
      have hinv : (((χ (g'⁻¹) : (↥K.1)ˣ) : ↥K.1) : Om l) = algebraMap F (Om l) y⁻¹ := by
        rw [map_inv, map_inv₀, hy, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      obtain ⟨w, hw⟩ := hunit ⟨y⁻¹, hle'⟩ g'⁻¹ (Subtype.ext (by rw [hρ, hinv]))
      refine ⟨w⁻¹, ?_⟩
      have hw2 : ((w : 𝒪[F]) : F) = y⁻¹ := by rw [hw]
      have hw3 : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((w : 𝒪[F]) : F) = 1 := by
        have h5 : ((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (w : 𝒪[F]) = 1 := Units.inv_mul w
        exact congrArg Subtype.val h5
      rw [hw2] at hw3
      rw [← hy, (eq_of_mul_inv_eq_one hw3)]
  refine ⟨u, hu, fun n x hx => ?_⟩
  have hgZ : lubinTateGalPointMap (hπ := hπ) hf g (Z (n + 1)) = (u : 𝒪[F]) • Z (n + 1) :=
    IdealPoint.ext (by
      rw [lubinTateGalPointMap_val, heval (u : 𝒪[F]) g' (Subtype.ext (by rw [hρ]; exact hu))]
      exact hg _)
  have hZt : Z (n + 1) ∈ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1) :=
    CharEx.mem_torsion hπ h0 hs' (n + 1) _ rfl
  have hZn : Z (n + 1) ∉ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1 - 1) := by
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, hpow]
    exact hZ1
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hZt hZn
  obtain ⟨a, rfl⟩ := hgen x (lubinTateTorsion_mono hπ hf n.le_succ hx)
  rw [map_smul, hgZ, smul_smul, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.LTHodge.UnitAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_mirUin_gpProj_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  intro k _ _ _ _ m j n
  obtain ⟨v, hv, e⟩ := GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip k m (j + 1) (n : Mir k (j + 1)) n.2
  exact ⟨⟨v, hv⟩, v.2, e⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedes
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SegExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow_nat (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  induction n with
  | zero => simp [nabs]
  | succ n ih => rw [pow_succ, pow_succ, nabs_mul', ih]

theorem norm_absPow_nat (n : ℕ) (u : kˣ) : ‖((absPow k ((n : ℕ) : ℂ) u : ℂˣ) : ℂ)‖ = nabs k u ^ n := by
  have h : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; rfl
  rw [h, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k u).le _),
    Real.rpow_natCast]

theorem cast_tri (l : ℕ) (hl : 0 < l) : (((l * (l - 1) / 2 : ℕ)) : ℝ) = (l : ℝ) * ((l : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ l * (l - 1) := (Nat.even_mul_pred_self l).two_dvd
  rw [Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hl]
  norm_num

theorem exponent_lseg (Δ : Segment k) (y : IrrGL k) (s e : ℝ) (t : kˣ) (c : ℂ) (ht : nabs k t < 1)
    (hL : IsLSeg Δ y.rep) (hc : Zl.ScalarBy Δ.first t c) (hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e))
    (hy : ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) :
    s = e + ((Δ.len : ℝ) - 1) / 2 := by
  have h1 := GlobalTheory.T.segment_rep_central_character k Δ y hL t c hc
  have h2 := hy t _ h1
  have hdeg : y.1 = Δ.len * Δ.d := hL.deg_eq.symm
  have hα : 0 < nabs k t := nabs_pos' k t
  have hlog : Real.log (nabs k t) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hα ht.ne
  rw [norm_mul, norm_pow, norm_absPow_nat, nabs_pow_nat, hcn, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_mul hα.le,
    ← Real.rpow_add hα] at h2
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow hα, Real.log_rpow hα] at h3
  have h4 := mul_right_cancel₀ hlog h3
  rw [cast_tri _ Δ.len_pos, hdeg] at h4
  have hl : (0 : ℝ) < Δ.len := by exact_mod_cast Δ.len_pos
  have hd : (0 : ℝ) < Δ.d := by exact_mod_cast Δ.d_pos
  push_cast at h4
  have h5 : (Δ.len : ℝ) * Δ.d * (s - (e + ((Δ.len : ℝ) - 1) / 2)) = 0 := by linear_combination -h4
  have h6 := (mul_eq_zero.1 h5).resolve_left (by positivity)
  linarith

theorem len_lt_of_precedes {Δ Δ' : Segment k} {j : ℕ} (hl : Δ.Linked Δ') (hf : Δ'.first = Δ.first.nu j) :
    Δ.len < j + Δ'.len := by
  by_contra hcon
  refine hl.2.2 fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
  refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
  rw [hf, IrrGL.nu_nu]
  push_cast
  rfl

theorem exponent_lt_of_precedes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL k) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  intro k _ _ _ _ Δ Δ' y y' s s' hL hL' hy hy' hP
  obtain ⟨hlink, j, hj, hf⟩ := hP
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hα1 : nabs k t < 1 := GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  have hα : 0 < nabs k t := nabs_pos' k t
  obtain ⟨e, he⟩ := GlobalTheory.T.central_character_norm_eq_pow k Δ.first Δ.isCusp_first.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.central_character_exists k Δ.first t
  have hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e) := he t c hc
  have hdd : Δ'.d = Δ.d := congrArg Sigma.fst hf
  have hc' : Zl.ScalarBy Δ'.first t (c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)) := by
    rw [hf]
    exact GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first _ t c hc
  have hcn' : ‖c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((Δ'.d : ℝ) * (e + j)) := by
    rw [norm_mul, norm_absPow_nat, nabs_pow_nat, hcn, hdd, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hα.le, ← Real.rpow_add hα]
    congr 1
    show (Δ.d : ℝ) * e + (Δ.d : ℝ) * j = _
    ring
  have h1 := exponent_lseg Δ y s e t c hα1 hL hc hcn hy
  have h2 := exponent_lseg Δ' y' s' (e + j) t _ hα1 hL' hc' hcn' hy'
  have h3 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast len_lt_of_precedes hlink hf
  have h4 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [h1, h2]
  linarith

end GlobalTheory.CompanionTheory.SegExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndepStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_sections_cotangent_indep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep | exact GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuousStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | exact GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | (intros; apply GlobalTheory.CompanionTheory.BZMir.continuous_gpProj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormulaStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_levi_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibGP.gpProj_levi | exact GlobalTheory.CompanionTheory.LeibGP.gpProj_levi | (intros; apply GlobalTheory.CompanionTheory.LeibGP.gpProj_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) → (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  first | exact @GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | exact GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.GpUnip.gpProj_unip <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjectiveStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : Mir k j), u ∈ MirUin k j → ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | exact GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosedStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_mirabolicParabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | exact GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | (intros; apply GlobalTheory.CompanionTheory.MirGP.isClosed_HGP <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBoundStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_of_norm_bound : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ ν : Fin n → ℤ, Antitone ν → DomLE (wtR ν) (m0 lam) → ∀ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) → ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (wtR ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 → ν ∈ harmZ lam := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | exact GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | (intros; apply GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge <;> assumption)
end

