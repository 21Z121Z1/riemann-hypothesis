import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ToLinNfMatEqSumNfGen
import Formalism.LocalToGlobal.Columns.LevGCount
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsModulusTopOfIsTotallyComplex
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.Mem.Chr GlobalTheory.Mem.LocTriv GlobalTheory.RayFromArtin
open scoped nonZeroDivisors

namespace GlobalTheory.UnramModulus

theorem inInertia_restrict {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (L : Type) [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G K Ω}
    (hσ : σ ∈ Ine (F := K) A) : GlobalTheory.NT.InInertia L v (AlgEquiv.restrictNormalHom L σ) := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  refine ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩
  · ext x
    rw [Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  · rw [hf]
    have := hσ.2 _ (valuation_int_le_one A x)
    rw [← σ.restrictNormal_commutes L, ← map_sub] at this
    exact this

theorem rayIdl_le {K : Type} [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) {U : Subgroup (Ideles K)}
    (ho : IsOpen (U : Set (Ideles K))) (hi : infConn K ≤ U)
    (hu : ∀ v x, IsUnitAt v x → localIdele K v x ∈ U) : rayIdl 𝔪 ≤ U := by
  rintro b ⟨hb, -, hb'⟩
  let c : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (infPart b)
  have e : b = c * finPartI K b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [e]
  refine mul_mem (hi ⟨_, hb', rfl⟩) ?_
  refine (U.isClosed_of_isOpen ho).mem_of_tendsto
    (tendsto_part (a := finPartI K b) hb fun _ => rfl) (Filter.Eventually.of_forall fun S => ?_)
  exact Subgroup.prod_mem _ fun v _ => hu v _ (hb v)

theorem isModulus_top (H : GlobalTheory.Published.GlobalArtinReciprocity) (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭)
    (χ : (M ≃ₐ[K] M) →* ℂˣ) : GlobalTheory.NT.IsModulus M χ ⊤ := by
  let Ω := AlgebraicClosure K
  obtain ⟨art, ha⟩ := H K Ω
  let j : M →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra M Ω := j.toRingHom.toAlgebra
  have : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : CommGroup (M ≃ₐ[K] M) := { (inferInstance : Group (M ≃ₐ[K] M)) with mul_comm := mul_comm' }
  let φ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hφ : Continuous φ := by
    refine continuous_of_isOpen_ker' φ ?_
    have : FiniteDimensional K j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun σ hσ => ?_) j.fieldRange.fixingSubgroup_isOpen
    ext x
    apply (algebraMap M Ω).injective
    exact (σ.restrictNormal_commutes M x).trans (hσ ⟨_, x, rfl⟩)
  let θ : Ideles K →* (M ≃ₐ[K] M) := (liftAb φ hφ).comp art
  have hθ : Continuous θ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (θ.ker : Set (Ideles K)) := (isOpen_discrete {1}).preimage hθ
  have hk : (diagUnits K).range ⊔ infConn K ≤ θ.ker := fun x hx => by
    have hk : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have hr : rayGrp ⊤ ≤ θ.ker := by
    refine sup_le (le_sup_left.trans hk) (rayIdl_le ⊤ ho (le_sup_right.trans hk) fun v x hx => ?_)
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨τ, hτ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← e, liftAb_toAb]
    exact hM v _ (inInertia_restrict M hA hτ)
  let ψ : idealsPrimeTo (⊤ : Ideal (𝓞 K)) →* (M ≃ₐ[K] M) := (θ.comp (unifIdl ⊤))⁻¹
  have hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn M 𝔭 ∧ GlobalTheory.NT.IsFrob M 𝔭 (ψ (primeElt ⊤ 𝔭 h)) := fun v hv => by
    refine ⟨hM v, ?_⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ, e'⟩ := (ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩
    have : ψ (primeElt ⊤ v hv) = AlgEquiv.restrictNormalHom M σ := by
      rw [MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, MonoidHom.comp_apply,
        ← e', liftAb_toAb, map_inv, inv_inv]
    rw [this]
    exact isFrob_restrict M hA hσ
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr' => ?_⟩
  · obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob M 𝔭
    rw [GlobalTheory.NT.heckeVal_of_unramIn M χ (hM 𝔭) hσ]
    exact Units.ne_zero _
  · have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr'.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr'.2.1
    obtain ⟨A, hA'⟩ := exists_integral ⊤ _ ha0 hr'.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral ⊤ _ hb0 hr'.2.2.2.1
    rw [heckeIdeal_eq M ⊤ ψ hψ χ _ ha0 A hA', heckeIdeal_eq M ⊤ ψ hψ χ _ hb0 B hB']
    have h1 : B⁻¹ * A ∈ (rayPrincipal ⊤).subgroupOf (idealsPrimeTo (⊤ : Ideal (𝓞 K))) := by
      rw [Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast hr'.1
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hr'.2.1
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr', by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    have h2 : ψ (B⁻¹ * A) = 1 := by
      rw [MonoidHom.inv_apply, inv_eq_one]
      exact hr ((unifIdl_mem_rayGrp_iff top_ne_bot _).2 h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]

theorem isModulus_top_of_isTotallyComplex : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (K M : Type) [Field K]
    [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M],
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭) → ∀ χ : (M ≃ₐ[K] M) →* ℂˣ, GlobalTheory.NT.IsModulus M χ ⊤ :=
  fun H K M _ _ _ _ _ _ _ hM χ => isModulus_top H K M hM χ

end GlobalTheory.UnramModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def IsNeg (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Prop := (-(Yᴴ * Jm P Q * Y)).PosDef

def matA (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ := Y.toRows₁ * (Y.toRows₂)⁻¹

def linX (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim (v ∘ Sum.inl - matA Y *ᵥ (v ∘ Sum.inr)) ((φ ∘ Sum.inl) ᵥ* matA Y + φ ∘ Sum.inr)

def scal (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : ℂ :=
  (Y.toRows₂.det)⁻¹ * Complex.exp (-((linX Y v φ ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)))

def ker (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ)
    (v' φ' : Ix P Q → ℂ) : ℂ :=
  ((-(Yᴴ * Jm P Q * Y')).det)⁻¹ * Complex.exp ((star v ᵥ* Jm P Q) ⬝ᵥ v' -
    (star v ᵥ* Jm P Q + φ') ⬝ᵥ (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) *ᵥ (Jm P Q *ᵥ star φ + v'))

def baseY (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Ix P Q) (Fin Q) ℂ := Matrix.fromRows A 1

def baseV (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim (x ∘ Sum.inl) 0

def baseF (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim 0 (x ∘ Sum.inr)

def dA (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ :=
  Z.toBlocks₁₁ * A + Z.toBlocks₁₂ - A * (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)

def dX (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim ((Z.toBlocks₁₁ - A * Z.toBlocks₂₁) *ᵥ (x ∘ Sum.inl))
    (-((x ∘ Sum.inr) ᵥ* (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)))

def dS (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : ℂ :=
  -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂).trace - (x ∘ Sum.inr) ⬝ᵥ Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)

theorem toRows₂_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : (baseY A).toRows₂ = 1 := rfl

theorem matA_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : matA (baseY A) = A := by
  simp [matA, baseY]

theorem linX_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : linX (baseY A) (baseV x) (baseF x) = x := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  have h2 : baseF x ∘ Sum.inl = 0 := rfl
  rw [linX, h1, h2]
  ext (i | j) <;> simp [baseV, baseF]

theorem scal_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : scal (baseY A) (baseV x) (baseF x) = 1 := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  simp [scal, h1, toRows₂_baseY]

theorem form_blocks (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * Y'.toRows₂ - Y.toRows₁ᴴ * Y'.toRows₁ := by
  conv_lhs => rw [← Matrix.fromRows_toRows Y, ← Matrix.fromRows_toRows Y']
  rw [Jm, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem frame_eq (Y : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) :
    Y = baseY (matA Y) * Y.toRows₂ := by
  rw [baseY, Matrix.fromRows_mul, matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one,
    Matrix.one_mul, Matrix.fromRows_toRows]

theorem form_factor (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) (h' : IsUnit Y'.toRows₂.det) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
  have e : ∀ Y : Matrix (Ix P Q) (Fin Q) ℂ, IsUnit Y.toRows₂.det → matA Y * Y.toRows₂ = Y.toRows₁ := fun Y h => by
    rw [matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  rw [form_blocks, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    e Y h, Matrix.mul_assoc, e Y' h']

theorem isNeg_baseY {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) : IsNeg (baseY A) := by
  rw [IsNeg, form_blocks]
  simpa [baseY] using h

theorem IsNeg.isUnit {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : IsUnit Y.toRows₂.det := by
  rw [IsNeg, form_blocks] at h
  have h2 := h.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self Y.toRows₁)
  rw [sub_add_cancel] at h2
  have h3 := h2.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h3
  exact isUnit_of_mul_isUnit_right h3

theorem IsNeg.posDef {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : (1 - (matA Y)ᴴ * matA Y).PosDef := by
  have hu := h.isUnit
  rw [IsNeg, form_factor Y Y hu hu] at h
  have hu' : IsUnit Y.toRows₂ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  exact (hu'.posDef_star_left_conjugate_iff).1 h

theorem form_mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    (g * Y)ᴴ * Jm P Q * (g * Y') = Yᴴ * Jm P Q * Y' := by
  rw [Matrix.conjTranspose_mul]
  conv_rhs => rw [← hg]
  simp only [Matrix.mul_assoc]

theorem IsNeg.mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) :
    IsNeg (g * Y) := by
  rwa [IsNeg, form_mul hg]

theorem Jm_mul_Jm : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem ker_mul {g g' : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (hg' : g' * g = 1)
    (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : Ix P Q → ℂ) :
    ker (g * Y) (g *ᵥ v) (φ ᵥ* g') (g * Y') (g *ᵥ v') (φ' ᵥ* g') = ker Y v φ Y' v' φ' := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg'
  have h1 : gᴴ * Jm P Q = Jm P Q * g' := by
    conv_rhs => rw [← hg, Matrix.mul_assoc, hg2, Matrix.mul_one]
  have h0 : g' = Jm P Q * gᴴ * Jm P Q := by
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have hJ : (Jm P Q)ᴴ = Jm P Q := by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h2 : Jm P Q * g'ᴴ = g * Jm P Q := by
    rw [h0, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have e1 : star (g *ᵥ v) ᵥ* Jm P Q = (star v ᵥ* Jm P Q) ᵥ* g' := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h1]
  have e2 : Jm P Q *ᵥ star (φ ᵥ* g') = g *ᵥ (Jm P Q *ᵥ star φ) := by
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]
  have e3 : g * Y' * (Yᴴ * Jm P Q * Y')⁻¹ * (g * Y)ᴴ * Jm P Q =
      g * (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) * g' := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h1]
  have e4 : ∀ (u w : Ix P Q → ℂ) (M : Mat P Q), (u ᵥ* g') ⬝ᵥ (g * M * g') *ᵥ (g *ᵥ w) = u ⬝ᵥ M *ᵥ w := by
    intro u w M
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg', Matrix.mul_one]
  rw [ker, ker, form_mul hg, e1, e2, e3, ← Matrix.add_vecMul, ← Matrix.mulVec_add, e4, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]

end GlobalTheory.OscGauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem isSchemeTheoreticallyDominant_compl_of_effCartier :
    ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I →
      IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  intro W I hI
  choose U f hxU hf hIU using hI
  refine ⟨le_bot_iff.1 (Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun x s hs => ?_)⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · have h0 := Scheme.Hom.ideal_ker_le _ (U x) hs
    rw [RingHom.mem_ker, Scheme.Opens.ι_app] at h0
    have hle : W.basicOpen (f x) ≤ (Scheme.Opens.ι (X := W) I.support.compl) ''ᵁ
        ((Scheme.Opens.ι (X := W) I.support.compl) ⁻¹ᵁ (U x).1) := by
      intro y hy
      have hyU : y ∈ (U x).1 := W.basicOpen_le (f x) hy
      have hyc : y ∈ I.support.compl := by
        intro hy'
        have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
        rw [Scheme.mem_zeroLocus_iff] at this
        exact this (f x) (by rw [hIU]; exact Ideal.subset_span rfl) hy
      exact ⟨⟨y, hyc⟩, hyU, rfl⟩
    have := (U x).2.isLocalization_basicOpen (f x)
    have hinj := IsLocalization.injective (M := Submonoid.powers (f x)) Γ(W, W.basicOpen (f x))
      ((Submonoid.powers_le).2 (hf x))
    have h1 : algebraMap Γ(W, (U x).1) Γ(W, W.basicOpen (f x)) s = 0 := by
      have h2 := congrArg (W.presheaf.map (homOfLE hle).op).hom h0
      have h3 := h2.trans (map_zero (W.presheaf.map (homOfLE hle).op).hom)
      refine Eq.trans ?_ h3
      erw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have : s = 0 := hinj (by rw [h1, map_zero])
    simp [this]

end GlobalTheory.ProjBlowup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormModuloUnipotentSemidirect
section
namespace GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect

theorem latticeNormalForm : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm :=
  GlobalTheory.Proof.LatticeNormalFormUnipotent.latticeNormalForm

end GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormViaMatrix
section
noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

theorem nfMat_eq_qnf {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) :
    nfMat n c q e z = GlobalTheory.QNF.nfMat n c q e z := by
  funext l s
  unfold nfMat GlobalTheory.QNF.nfMat
  by_cases hs : s.1 < n
  · simp [hs]
  · by_cases hls : l = s
    · subst hls
      simp [hs, Loc.inX]
    · by_cases hn : s.1 = n
      · by_cases hl : l.1 < n
        · simp [hls, hn, hl, Loc.inX]
        · simp [hls, hn, hl, Loc.inX]
      · simp [hs, hls, hn]

theorem nf_matrix : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → ∃ (e : Fin (cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (fun l : Fin (R.N j + cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ∧ (lamYat (Pr := Pr) (R := R) j P).map (h.toLinearMap.restrictScalars (𝓞 X.E)) = (lamYat (Pr := Pr) (R := R) j P).map ((Matrix.toLin' (nfMat (R.N j) (cOf R j) (qOf P : X.E) e z)).restrictScalars (𝓞 X.E)) := by
  intro X Pr R j P hP h hh
  obtain ⟨e, z, h1, h2, h3⟩ := (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 hh
  exact ⟨e, z, h1, h2, by rw [nfMat_eq_qnf]; exact h3⟩

end GlobalTheory.Mem.Col2.IdxEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterStepZeroTypePrime
section
noncomputable section

namespace GlobalTheory.Proof.levelCharacter_stepZero_typePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem supSum_range {κ : Type} [CommRing κ] {n a k : ℕ} (hn : k ≤ n) (ha : k ≤ a) (M : Matrix (Fin n) (Fin n) κ) (f : ℕ → κ)
    (hf : ∀ (i : ℕ) (h : i + 1 < k), f i = M ⟨i, by omega⟩ ⟨i + 1, by omega⟩) :
    supSum a (Finset.range (k - 1)) M = ∑ i ∈ Finset.range (k - 1), f i := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < a ∧ i.val ∈ Finset.range (k - 1) then M i j else 0) =
      if i.val ∈ Finset.range (k - 1) then f i.val else 0 := by
    intro i
    by_cases hi : i.val ∈ Finset.range (k - 1)
    · have hi' := Finset.mem_range.1 hi
      rw [if_pos hi, Finset.sum_eq_single (⟨i.val + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by dsimp only; omega, hi⟩,
        hf _ (by omega)]
      · intro j _ hj
        exact if_neg fun h => hj (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => if i ∈ Finset.range (k - 1) then f i else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

variable {E : Type} [Field E]

theorem entB_X (q : ℕ) {k n c i : ℕ} (hn : k ≤ n) (hi : i + 1 < k) (ex : ℕ → ℕ) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n ex ex x i (i + 1) = Loc.atN (x (Loc.eN E (n + c) (i + 1))) i := by
  have e1 : LocE.fIdx k c n i = i := if_pos (by omega)
  have e2 : LocE.fIdx k c n (i + 1) = i + 1 := if_pos hi
  have e3 : LocE.scE n ex i = 0 := if_pos (by omega)
  have e4 : LocE.scE n ex (i + 1) = 0 := if_pos (by omega)
  unfold LocE.entB
  rw [e1, e2, e3, e4]
  simp

theorem symLevelFrameEntry_superdiag_second_block (q : ℕ) {k n c i : ℕ} (hi : i + 1 < c) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n (fun i => i + 1) (fun i => i + 1) x (k + i) (k + i + 1) =
      (q : E) * Loc.atN (x (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have e1 : LocE.fIdx k c n (k + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e2 : LocE.fIdx k c n (k + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e3 : LocE.scE n (fun i => i + 1) (n + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    beta_reduce
    omega
  unfold LocE.entB
  rw [e1, e2, e3, zpow_one, mul_comm]

theorem chrG_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true)
    (hψ : ∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) :
    ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  have hm := R.two_le_m
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hc : R.r - R.k - 1 = cOf R 0 - 1 := by unfold Ranks.r cOf; omega
  have hl : colLev Ch 0 ⟨P.1, hP⟩ = ⟨HX (𝓞 X.E ⧸ P.1.asIdeal) (R.N 0) R.k R.t 0,
      lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0⟩ := if_pos (by omega)
  rw [hl]
  intro hbar g r hr hrg hg
  have hq : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hp0 : psi0P Ch P.1 = Ch.psi0 ⟨P.1, hP⟩ := dif_pos hP
  have hJ := hr.2
  simp only [Jat, hP, hs, if_true] at hJ
  have hst : r ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N 0) (cOf R 0) fun i => i + 1) := by
    have h1 := hJ.1
    simpa using h1
  have hint := fun p p' => GlobalTheory.LastSteps.entB_int (P := P.1) R.k (x := r.toLinearMap) (fun y hy => (hst y).2 hy) p p'
  have ha := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r hst
  have h2 : ∑ i ∈ Finset.range (R.r - R.k - 1), LocE.entB (qOf P.1) R.k (cOf R 0) (R.N 0) (cOf R 0) (R.N 0)
      (fun i => i + 1) (fun i => i + 1) r.toLinearMap (R.k + i) (R.k + i + 1) = (qOf P.1 : X.E) * Loc.n1Arg r := by
    rw [hc, Loc.n1Arg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    exact symLevelFrameEntry_superdiag_second_block _ (by omega) _
  have h3 : cst.psi P (Loc.n1Arg r) = psi0P Ch P.1 (redP P.1 ((qOf P.1 : X.E) * Loc.n1Arg r)) := by
    rw [← hψ _ ha, mul_div_cancel_left₀ _ hq]
  have h4 : ((lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0 hbar : X.Kˣ) : X.K) =
      Ch.psi0 ⟨P.1, hP⟩ (supSum R.k (Finset.range (R.k - 1)) hbar.1.1) := by
    show ((lamGen _ _ _ R.k [] (SX R.k R.m 0) hbar : X.Kˣ) : X.K) = _
    rw [lamGen_nil, SX_zero]
    rfl
  refine h4.trans ?_
  simp only [chiInv, lamRow, hP, hs, if_true, LocE.lamGBS, LocE.lamGvS, inv_one, one_mul, mul_one, Finset.range_zero,
    Finset.prod_empty]
  rw [h2, h3, hp0, reduction_add (GlobalTheory.TopStep.intAt_sum _ fun i _ => hint _ _) ha, AddChar.map_add_eq_mul,
    GlobalTheory.TopStep.reduction_sum₂ _ fun i _ => hint _ _, mul_comm, mul_inv_cancel_right₀ (AddChar.val_isUnit _ _).ne_zero]
  congr 1
  refine supSum_range hN.ge le_rfl _ _ fun i hi => ?_
  have hi1 : i + 1 < R.N 0 := by omega
  have hi0 : i < R.N 0 := by omega
  have he : Loc.eN X.E (R.N 0 + cOf R 0) (i + 1) = Loc.inX X.E (R.N 0) (cOf R 0) (Loc.eN X.E (R.N 0) (i + 1)) := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply]
    unfold Loc.eN
    split_ifs <;> first | rfl | omega
  have hv : redV P.1 (Loc.eN X.E (R.N 0) (i + 1)) = Pi.single ⟨i + 1, hi1⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact GlobalTheory.TopStep.reduction_one₂
    · exact GlobalTheory.TopStep.reduction_zero
  have h5 := congrFun (hg _ (GlobalTheory.GO.ChRoot.eN_mem (i := i + 1))) ⟨i, hi0⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  rw [entB_X _ hN.ge hi, he, LinearEquiv.coe_coe, hrg, Loc.atN, dif_pos (by omega), GlobalTheory.QNormal.inX_apply, dif_pos hi0]
  exact h5

end GlobalTheory.Proof.levelCharacter_stepZero_typePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonempty
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Mem

theorem nonempty_locStage : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  have h := GlobalTheory.T.exists_local_prime_ainf
  choose P AI hT using h
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosureStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_field_over_place_alg_closure : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first | exact @GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | exact GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | (intros; apply GlobalTheory.ResidueBar.residueField_ringEquiv_fbar <;> assumption)
end

