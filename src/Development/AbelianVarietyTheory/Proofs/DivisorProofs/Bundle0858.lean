import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.TranslQuotient

theorem finiteSubsets_preimage {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hamp : Out.RelAmple A L) (U : S.Opens) (hU : IsAffineOpen U) :
    FiniteSubsetsInAffineOpens (A.hom ⁻¹ᵁ U) := by
  have h := GlobalTheory.isAmpleLB_of_relAmple A hL hamp U hU
  exact ⟨fun s hs => by
    obtain ⟨n, -, t, h1, -, h2⟩ := h.exists_affine_finite_subset hs (U := ⊤) (Set.subset_univ _)
    exact ⟨_, h2, h1⟩⟩

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    Hecke.transl (a * c) = Hecke.transl a ≫ Hecke.transl c := by
  simp only [Hecke.transl, comp_mul, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit A)]
  exact (mul_assoc _ _ _).symm

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] :
    Hecke.transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  simp [Hecke.transl]

theorem isAbelianScheme_of_finite_etale {S : Scheme.{0}} (A Q : Over S) [GrpObj A] [GrpObj Q]
    (q : A ⟶ Q) (hA : IsAbelianScheme A) (hQ : IsCommMonObj Q) (hfin : IsFinite q.left)
    (het : Etale q.left) (hsurj : Surjective q.left) : IsAbelianScheme Q := by
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : IsSeparated (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := GlobalTheory.NilProper.isSeparated_of_comp_surjective q.left Q.hom
  have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom :=
    GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Q.hom hfin inferInstance inferInstance hsurj inferInstance
  exact ⟨hQ, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Q, ⟨⟩,
    GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Q.hom⟩

open GlobalTheory.AbelianQuotient in

theorem grp_descent : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A] (q : A ⟶ Q),
    Flat q.left → Surjective q.left → QuasiCompact q.left →
    (∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q) →
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q := by
  intro S A Q _ _ q _ _ _ hq
  have hinv : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q → a⁻¹ ≫ q = b⁻¹ ≫ q := by
    intro W a b h
    have h1 : (a⁻¹ * a) ≫ q = (a⁻¹ * b) ≫ q := hq W _ _ _ _ rfl h
    have h2 := hq W b⁻¹ b⁻¹ (a⁻¹ * b) (a⁻¹ * a) rfl h1.symm
    have e1 : b⁻¹ * (a⁻¹ * b) = a⁻¹ := by rw [mul_left_comm, inv_mul_cancel, _root_.mul_one]
    have e2 : b⁻¹ * (a⁻¹ * a) = b⁻¹ := by rw [inv_mul_cancel, _root_.mul_one]
    rwa [e1, e2] at h2
  have hμ : ∀ {W : Over S} (x : W ⟶ A ⊗ A), x ≫ μ[A] = (x ≫ fst A A) * (x ≫ snd A A) := by
    intro W x
    rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    have h1 : (a ≫ fst A A) ≫ q = (b ≫ fst A A) ≫ q := by simpa using h =≫ fst Q Q
    have h2 : (a ≫ snd A A) ≫ q = (b ≫ snd A A) ≫ q := by simpa using h =≫ snd Q Q
    rw [← Category.assoc, ← Category.assoc, hμ a, hμ b]
    exact hq W _ _ _ _ h1 h2)
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def]
    exact hinv a b h)
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom⟩
  rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
    IsCommMonObj.mul_comm_assoc]

theorem comp_transl {S : Scheme.{0}} {A W : Over S} [GrpObj A] (x : W ⟶ A) (h : 𝟙_ (Over S) ⟶ A) :
    x ≫ Hecke.transl h = x * (toUnit _ ≫ h) := by
  rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit _)]

theorem transl_compat : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A]
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (q : A ⟶ Q),
    GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) q.left →
    ∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q := by
  intro S A Q _ _ H q hc W a b c d hab hcd
  have loc := (GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hc).2.1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p ↦ ?_
  obtain ⟨V₁, h, hp₁, e₁⟩ := loc W.left a.left b.left (congrArg CommaMorphism.left hab) p
  obtain ⟨V₂, k, hp₂, e₂⟩ := loc W.left c.left d.left (congrArg CommaMorphism.left hcd) p
  refine ⟨V₁ ⊓ V₂, ⟨hp₁, hp₂⟩, ?_⟩
  let jV : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ W := Over.homMk (V₁ ⊓ V₂).ι rfl
  have f₁ : jV ≫ b = (jV ≫ a) * (toUnit _ ≫ h.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_left : V₁ ⊓ V₂ ≤ V₁), ]
    simp only [Category.assoc, e₁]
  have f₂ : jV ≫ d = (jV ≫ c) * (toUnit _ ≫ k.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_right : V₁ ⊓ V₂ ≤ V₂), ]
    simp only [Category.assoc, e₂]
  have hinv : Hecke.transl (h * k).1 ≫ q = q := Over.OverMorphism.ext (hc.inv (h * k))
  have key : jV ≫ (b * d) = jV ≫ (a * c) ≫ Hecke.transl (h * k).1 := by
    rw [comp_mul, f₁, f₂, ← Category.assoc, comp_transl, comp_mul, Subgroup.coe_mul, comp_mul,
      _root_.mul_mul_mul_comm]
  have key' : jV ≫ (a * c) ≫ q = jV ≫ (b * d) ≫ q := by
    rw [← Category.assoc jV (b * d), key, Category.assoc, Category.assoc, hinv]
  simpa [jV] using congrArg CommaMorphism.left key'

theorem exists_quotient : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  intro S A _ _ L H hA hL hamp hH hfree
  let ρ : H → (A.left ⟶ A.left) := fun h => (Hecke.transl h.1).left
  have h1 : ρ 1 = 𝟙 _ := by
    show (Hecke.transl (1 : 𝟙_ (Over S) ⟶ A)).left = _
    rw [transl_one]; rfl
  have hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c := fun a c => by
    show (Hecke.transl (a.1 * c.1)).left = _
    rw [transl_mul]; rfl
  have hS : ∀ a, ρ a ≫ A.hom = A.hom := fun a => Over.w _
  let τ := GlobalTheory.ZM.autOfRightAction ρ h1 hm
  have hτ : ∀ a, (τ a).hom ≫ A.hom = A.hom := fun a => hS a⁻¹
  have : OrbitsInAffineOpens τ := OrbitsInAffineOpens.of_locally_on_base τ A.hom hτ fun s => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    exact ⟨U, hsU, finiteSubsets_preimage A L hL hamp U hU⟩
  have hfreeρ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ A.left) (a : H),
      y ≫ ρ a = y → a = 1 := by
    intro k _ _ y a hy
    let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    have e : y' ≫ Hecke.transl a.1 = y' := Over.OverMorphism.ext hy
    have e' : y' ≫ Hecke.transl a.1 = y' * (toUnit _ ≫ a.1) := by
      rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (y' ≫ toUnit A) (toUnit _)]
    rw [e'] at e
    have h2 : toUnit (Over.mk (y ≫ A.hom)) ≫ a.1 = 1 := mul_eq_left.mp e
    exact Subtype.ext (hfree k (y ≫ A.hom) a.1 a.2 h2)
  have hf : IsFreeAction τ := .of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfreeρ k y a⁻¹ h)
  let ψ : A ⟶ Over.mk (finiteQuotient.desc τ A.hom hτ) :=
    Over.homMk (finiteQuotient.π τ) (finiteQuotient.π_desc τ A.hom hτ)
  have hc : GlobalTheory.ZM.IsGaloisCover H ρ ψ.left := by
    refine ⟨hH, h1, hm, fun a ↦ ?_, finiteQuotient.isFinite_π_of_isFreeAction hf,
      finiteQuotient.etale_π hf, inferInstanceAs (Surjective (finiteQuotient.π τ)),
      fun k _ _ y y' e ↦ ?_⟩
    · have := finiteQuotient.comp_π τ a⁻¹
      rwa [GlobalTheory.ZM.autOfRightAction_hom, inv_inv] at this
    · obtain ⟨a, ha⟩ := (finiteQuotient.comp_π_eq_iff τ y y').mp e
      have ha : y ≫ ρ a⁻¹ = y' := ha
      refine ⟨a⁻¹, ha, fun c hc ↦ ?_⟩
      have hc : y ≫ ρ c = y' := hc
      have : y ≫ ρ (c * a) = y := by
        rw [hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfreeρ k y _ this)
  have := hc.fin
  have := hc.etale
  have := hc.onto
  obtain ⟨inst, hcomm, hhom⟩ := grp_descent S A _ ψ inferInstance hc.onto inferInstance
    (transl_compat S A _ H ψ hc)
  exact ⟨_, inst, hcomm, ψ, isAbelianScheme_of_finite_etale A _ ψ hA hcomm hc.fin hc.etale hc.onto,
    hhom, hc⟩

end GlobalTheory.TranslQuotient

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_rational_middle_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  intro F E _ _ _ _ _ σ hσ K _ _ _ hd M J hM hJ hu x y hx hy
  obtain ⟨w, h1, h2⟩ := GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian F E σ hσ K M J hM hJ hu x y hx hy
  obtain ⟨z, hz, n1, n2⟩ := GlobalTheory.T.unitNorm_gramDet_rational_approximation F E σ hσ K hd M J hJ x y hx w h1 h2
  exact ⟨z, hz, GlobalTheory.T.unitNorm_gramDet_plane_reduction F E σ hσ K M J hJ x z hx n1, GlobalTheory.T.unitNorm_gramDet_plane_reduction F E σ hσ K M J hJ z y hz n2⟩

end GlobalTheory.PlaneNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIpAtNonneg
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)
open scoped ComplexOrder

namespace GlobalTheory.ColumnFamilyMetric

open GlobalTheory.PeriodClassSum GlobalTheory.TestLat.Compare

theorem chF_gramV (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (b : (chF W sel mu I u j).β) :
    ((chF W sel mu I u j).mem b).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u j) := by
  ext i k
  have e : gramKd X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  show pairK (W.lamTrue u j) (gramKd X.emb 1) (bVV _ _ i) (bVV _ _ k) = _
  rw [e]
  exact pairK_one_basis (W.lamTrue u j) i k

theorem famIpAt_nonneg : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok) (v : InfinitePlace X.K) (φ : (chF W sel mu I u j).Forms), 0 ≤ (famIpAt (chF W sel mu I u j) h v φ φ).re := by
  intro X Pr R W sel Sg mu I u j h v φ
  refine (Complex.nonneg_iff.1 ?_).1
  unfold famIpAt
  refine Finset.sum_nonneg fun b _ => ?_
  have hG : ((((chF W sel mu I u j).mem b).gramV).map v.embedding).PosSemidef := by
    rw [chF_gramV]
    exact (gramB_posDef (W.lamTrue u j) v.embedding).posSemidef
  letI := (h b).fintypeCl
  exact (ipAt_eq _ (h b) v _ _).symm ▸ wForm_nonneg _ hG _

end GlobalTheory.ColumnFamilyMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.PicFin

variable {E : Type} [Field E] [NumberField E]

theorem mul_mem_hatO {c : Ideal (OF E)} {n : OF E} (hn : n ∈ c) {y : Af E}
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c := by
  refine GlobalTheory.IntDense.mem_of_isClosed E (C := {y | algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun b => ?_) y hy
  show _ * _ ∈ hatO c
  rw [← map_mul]
  refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), ?_⟩)
  rw [map_zero, zero_add, map_mul]
  rfl

def intR (E : Type) [Field E] [NumberField E] : Subring (Af E) where
  carrier := {y | ∀ v, y v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem finite_quot {N : ℕ} (hN : N ≠ 0) : Finite (intR E ⧸ Ideal.span {(N : intR E)}) := by
  have hi : ∀ a : 𝓞 E, algebraMap (𝓞 E) (Af E) a ∈ intR E := fun a v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one a))
  let f : 𝓞 E →+* intR E := (algebraMap (𝓞 E) (Af E)).codRestrict _ hi
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)}) (Ideal.span {(N : intR E)}) f
    ((Ideal.span_singleton_le_iff_mem _).2 (by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _))) fun x => ?_
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E N (Nat.pos_of_ne_zero hN)).2 α.1 α.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨β, hβ⟩, Subtype.ext ?_⟩
  show α.1 - algebraMap (𝓞 E) (Af E) a = (N : Af E) * β
  rw [e, ← nsmul_eq_mul]
  exact add_sub_cancel_left _ _

theorem mem_intR {u : (Af E)ˣ} (h : GlobalTheory.Idele.idealOf u = 1) : (u : Af E) ∈ intR E := fun v => by
  have h1 := (GlobalTheory.Idele.smul_eq_self_iff u (I := 1) one_ne_zero).1 (by rw [GlobalTheory.Idele.smul_one_eq, h]) v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1.le

theorem mem_sup {a : (Af E)ˣ} {x : E} (hx : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 E)⁰ x) :
    a ∈ ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx.trans (FractionalIdeal.spanSingleton_zero))
  obtain ⟨b, hb⟩ : ∃ b : (Af E)ˣ, b = FiniteAdeleRing.unitEmbedding (𝓞 E) E (Units.mk0 x hx0) := ⟨_, rfl⟩
  have h2 : GlobalTheory.Idele.idealOf (a * b⁻¹) = 1 := by
    rw [GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hb, GlobalTheory.Idele.idealOf_unitEmbedding, hx]
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have h3 : GlobalTheory.Idele.idealOf (a * b⁻¹)⁻¹ = 1 := by rw [GlobalTheory.Idele.idealOf_inv, h2, inv_one]
  have h4 : a * b⁻¹ ∈ (intR E).toSubmonoid.units := (Submonoid.mem_units_iff _ _).2 ⟨mem_intR h2, mem_intR h3⟩
  have h5 : b ∈ princ := MonoidHom.mem_range.2 ⟨Units.mk0 x hx0, by rw [hb]; exact Units.ext (by simp)⟩
  have h6 := Subgroup.mul_mem_sup h4 h5
  rwa [inv_mul_cancel_right] at h6

theorem finiteIndex_top : ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ).FiniteIndex := by
  classical
  let g : (Af E)ˣ →* ClassGroup (𝓞 E) := (ClassGroup.mk E).comp (GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits
  have : g.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := g.ker) fun a ha => ?_
  have h1 : ClassGroup.mk E ((GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  exact mem_sup hx

theorem finiteIndex_units {c : Ideal (OF E)} (hc : c ≠ ⊥) :
    ((hatOUnits c).subgroupOf (intR E).toSubmonoid.units).FiniteIndex := by
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have := finite_quot (E := E) hN
  let r : (intR E).toSubmonoid.units →* intR E ⧸ Ideal.span {((Ideal.absNorm c : ℕ) : intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), u.2.1⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have key : ∀ u ∈ r.toHomUnits.ker, ((u.1 : (Af E)ˣ) : Af E) ∈ hatO c := fun u hu => by
    have h2 : Ideal.Quotient.mk (Ideal.span {((Ideal.absNorm c : ℕ) : intR E)}) ⟨(u.1 : Af E), u.2.1⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = ((Ideal.absNorm c : ℕ) : Af E) * β.1 := congrArg Subtype.val hβ
    have h4 := mul_mem_hatO (Ideal.absNorm_mem c) β.2
    rw [map_natCast, map_natCast, ← h3] at h4
    simpa using add_mem h4 (one_mem _)
  exact Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu => ⟨key u hu, key u⁻¹ (inv_mem hu)⟩

theorem finite_picO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  intro E _ _ _ c hc
  let U : Subgroup (Af E)ˣ := (intR E).toSubmonoid.units
  let K : Subgroup (Af E)ˣ := princ ⊔ hatOUnits c
  have h1 := finiteIndex_units hc
  have h2 : (K.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := (hatOUnits c).subgroupOf U) (Subgroup.comap_mono le_sup_right)
  have := finiteIndex_top (E := E)
  have h3 : (U ⊔ K).FiniteIndex := Subgroup.finiteIndex_of_le (H := U ⊔ princ) (sup_le_sup_left le_sup_left _)
  have : K.FiniteIndex := ⟨by
    rw [← Subgroup.relIndex_mul_index (le_sup_right : K ≤ U ⊔ K), Subgroup.relIndex_sup_right]
    exact mul_ne_zero h2.1 h3.1⟩
  exact Subgroup.finite_quotient_of_finiteIndex

end GlobalTheory.CMVal.PicFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoverDeg

def GoodCover {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ)
    (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
    (∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale) ∧
    (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
    (letI := (π.app U).hom.toAlgebra
     Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = δ)

end GlobalTheory.CoverDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmple
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.AmpleTwistLB

theorem ample_pow_div : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  intro W S _ _ f A hA N M hN hM hcls hV
  have : CompactSpace S := hA.compactSpace
  choose V hzV hVa hVL using hV
  have loc : ∀ z : S, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow A n).Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ≤ V z ∧ IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) :=
    fun z => hA.exists_affine_le (hzV z)
  choose n hn s hzs hsV hsa using loc
  obtain ⟨T₀, hT₀⟩ := exists_finset_iSup_eq_top (fun z => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)) hzs
  obtain ⟨K, hK, t, ht⟩ := exists_common_pow (fun z : T₀ => n z) (fun z => hn z) (fun z => s z)
  have hAK := isLB_lbPow hA.isLB K
  have hG : ((lbPow A K).pull f).IsLB := LB.isLB_pull hAK f
  have hGgen : IsGenerated ((lbPow A K).pull f) :=
    (isGenerated_of_finite t (by simp only [ht]; exact hT₀)).pull f
  have hMK := isLB_lbPow hM K
  obtain ⟨c, hc⟩ := RelAmpleQProj.exists_isAmpleLB_tw hMK hG fun y => by
    obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (hT₀.ge (Set.mem_univ (f y)))
    refine ⟨secPull (t z) f, f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z), by rw [nonzeroLocus_secPull, ht], hz, ?_⟩
    have := GlobalTheory.ZH.CombLocus.isAffineHom_homOfLE f (hsV z) (hsa z) (hVa z)
    have h₁ : IsAmpleLB ((M.pull (f ⁻¹ᵁ V z).ι).pull (W.homOfLE (f.preimage_mono (hsV z)))) :=
      (hVL z).pull_of_isAffineHom _
    have h₂ : IsAmpleLB (M.pull (f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)).ι) :=
      h₁.of_lbIso (LB.isLB_pull hM _) (GenSpread.lbIso_pull_pull hM _ (Scheme.homOfLE_ι _ _).symm)
    exact ((isAmpleLB_pow_iff (LB.isLB_pull hM _) hK).2 h₂).of_lbIso (LB.isLB_pull hMK _)
      (lbIso_lbPow_pull hM _ K).symm
  refine ⟨c, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hAf : (A.pull f).IsLB := LB.isLB_pull hA.isLB f
  have hD : (LB.div (lbPow (A.pull f) (c + k)) N).IsLB := LB.isLB_div (isLB_lbPow hAf (c + k)) hN
  refine (isAmpleLB_pow_iff hD hK).1 ?_
  have hT := AbLaw.isLB_tw hMK hG (c : ℤ)
  have hGk := isLB_lbPow hG k
  have eG : CechPic.cls _ hG = K • CechPic.cls _ hAf := by
    rw [CechPic.cls_pull hAK f, CechPic.cls_lbPow hA.isLB, map_nsmul, ← CechPic.cls_pull hA.isLB f]
  have eT : CechPic.cls _ hT = CechPic.cls _ hMK + (c : ℤ) • CechPic.cls _ hG := by
    have e := CechPic.cls_div hMK (AbLaw.isLB_pw hG (-(c : ℤ))) hT
    rw [AmpleStabFinite.cls_pw] at e
    exact e.trans (by rw [neg_smul, sub_neg_eq_add])
  refine hc.tensor_isGenerated (hGgen.pow k) (isLB_lbPow hD K) ((CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk)).1 ?_)
  rw [CechPic.cls_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk, CechPic.cls_div (isLB_lbPow hD K) hT,
    CechPic.cls_lbPow hD, CechPic.cls_lbPow hG, eT, CechPic.cls_lbPow hM, eG, CechPic.cls_div (isLB_lbPow hAf (c + k)) hN hD,
    CechPic.cls_lbPow hAf, hcls]
  module

end GlobalTheory.AmpleTwistLB
end

