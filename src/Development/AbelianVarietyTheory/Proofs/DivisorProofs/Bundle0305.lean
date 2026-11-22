import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPi
section
noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

namespace TraceOpenPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}

def comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : ℍ[R i, a i, b i] :=
  ⟨x.re i, x.imI i, x.imJ i, x.imK i⟩

def glue (u : ∀ i, ℍ[R i, a i, b i]) : ℍ[∀ i, R i, a, b] :=
  ⟨fun i => (u i).re, fun i => (u i).imI, fun i => (u i).imJ, fun i => (u i).imK⟩

theorem glue_comp (x : ℍ[∀ i, R i, a, b]) : glue (fun i => comp i x) = x := by
  ext <;> rfl

theorem nrm_comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : nrm (comp i x) = nrm x i := by
  simp [nrm, comp]

theorem nrm_glue (u : ∀ i, ℍ[R i, a i, b i]) : nrm (glue u) = fun i => nrm (u i) := by
  funext i
  simp [nrm, glue]

theorem coords_glue (u : ∀ i, ℍ[R i, a i, b i]) : coords (glue u) = fun k i => coords (u i) k := by
  funext k i
  fin_cases k <;> rfl

theorem continuous_glue [∀ i, TopologicalSpace (R i)] :
    Continuous (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b]) := by
  refine continuous_induced_rng.2 ?_
  have : (coords ∘ (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b])) =
      fun u k i => coords (u i) k := by
    funext u
    exact coords_glue u
  rw [this]
  refine continuous_pi fun k => continuous_pi fun i => ?_
  have hc : Continuous (coords : ℍ[R i, a i, b i] → Fin 4 → R i) := continuous_induced_dom
  exact ((continuous_apply k).comp hc).comp (continuous_apply i)

end TraceOpenPi

open TraceOpenPi in

theorem traceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i),
    (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  intro ι _ R _ _ a b h g hg W hW
  have hgi : ∀ i, nrm (comp i g) = 1 := fun i => by
    rw [nrm_comp, hg]; rfl
  have hW' : glue ⁻¹' W ∈ 𝓝 (fun i => comp i g) := by
    refine continuous_glue.continuousAt.preimage_mem_nhds ?_
    rw [glue_comp]; exact hW
  rw [nhds_pi, Filter.mem_pi] at hW'
  obtain ⟨I, -, V, hV, hVW⟩ := hW'
  have hO := fun i => h i (comp i g) (hgi i) (V i) (hV i)
  choose O hOo hOn hOt using hO
  refine ⟨Set.univ.pi O, isOpen_set_pi Set.finite_univ fun i _ => hOo i,
    Set.univ_pi_nonempty_iff.2 hOn, fun t ht => ?_⟩
  have ht' := fun i => hOt i (t i) (ht i (Set.mem_univ i))
  choose u huV hun hur using ht'
  refine ⟨glue u, hVW fun i _ => huV i, ?_, ?_⟩
  · rw [nrm_glue]; funext i; exact hun i
  · funext i; exact hur i

end GlobalTheory.QSA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProd
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA.TraceOpenProd

variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}

def glue (p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂]) : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)] :=
  ⟨(p.1.re, p.2.re), (p.1.imI, p.2.imI), (p.1.imJ, p.2.imJ), (p.1.imK, p.2.imK)⟩

def fst (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : ℍ[R₁, a₁, b₁] :=
  ⟨x.re.1, x.imI.1, x.imJ.1, x.imK.1⟩

def snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : ℍ[R₂, a₂, b₂] :=
  ⟨x.re.2, x.imI.2, x.imJ.2, x.imK.2⟩

theorem glue_fst_snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : glue (fst x, snd x) = x := by
  ext <;> rfl

theorem nrm_glue (p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂]) : nrm (glue p) = (nrm p.1, nrm p.2) := by
  ext <;> simp [nrm, glue]

theorem nrm_fst (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : nrm (fst x) = (nrm x).1 := by
  simp [nrm, fst]

theorem nrm_snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : nrm (snd x) = (nrm x).2 := by
  simp [nrm, snd]

theorem continuous_coord {R : Type} [CommRing R] [TopologicalSpace R] {a b : R} (i : Fin 4) :
    Continuous (fun x : ℍ[R, a, b] => coords x i) :=
  (continuous_apply i).comp continuous_induced_dom

theorem continuous_glue : Continuous (glue : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] → _) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  have h1 : Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords p.1 i) :=
    (continuous_coord i).comp continuous_fst
  have h2 : Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords p.2 i) :=
    (continuous_coord i).comp continuous_snd
  have : (fun p => coords (glue p) i) =
      fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => (coords p.1 i, coords p.2 i) := by
    funext p
    fin_cases i <;> rfl
  show Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords (glue p) i)
  rw [this]
  exact h1.prodMk h2

end GlobalTheory.QSA.TraceOpenProd

namespace GlobalTheory.QSA

open TraceOpenProd in

theorem traceOpen_prod : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
    (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by
  intro R₁ R₂ _ _ _ _ a₁ b₁ a₂ b₂ h₁ h₂ g hg W hW
  have hW' : glue ⁻¹' W ∈ 𝓝 (fst g, snd g) := by
    apply continuous_glue.continuousAt.preimage_mem_nhds
    rw [glue_fst_snd]; exact hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := mem_nhds_prod_iff.1 hW'
  have hg₁ : nrm (fst g) = 1 := by rw [nrm_fst, hg]; rfl
  have hg₂ : nrm (snd g) = 1 := by rw [nrm_snd, hg]; rfl
  obtain ⟨O₁, hO₁, hne₁, hO₁t⟩ := h₁ _ hg₁ W₁ hW₁
  obtain ⟨O₂, hO₂, hne₂, hO₂t⟩ := h₂ _ hg₂ W₂ hW₂
  refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, hne₁.prod hne₂, ?_⟩
  rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
  obtain ⟨u₁, hu₁W, hu₁n, hu₁r⟩ := hO₁t t₁ ht₁
  obtain ⟨u₂, hu₂W, hu₂n, hu₂r⟩ := hO₂t t₂ ht₂
  refine ⟨glue (u₁, u₂), hsub ⟨hu₁W, hu₂W⟩, ?_, ?_⟩
  · rw [nrm_glue, hu₁n, hu₂n]; rfl
  · simp [glue, hu₁r, hu₂r]

end GlobalTheory.QSA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGenericPointStalkSubsetOfDenseOpen
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem range_jK_fromSpecStalk_subset_of_dense_range {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S]
    [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (s : S) :
    Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆
      Set.range j := by
  rintro _ ⟨x, rfl⟩
  have hZ : irreducibleComponent s ∈ irreducibleComponents S :=
    irreducibleComponent_mem_irreducibleComponents s
  have hZo : IsOpen (irreducibleComponent s) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgs : hZ.1.genericPoint ⤳ s := hg.specializes mem_irreducibleComponent
  have hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]; exact hgs
  obtain ⟨p, hp⟩ := hgr
  have hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_
    show Ideal.comap _ x.asIdeal ≤ p.asIdeal
    have hx0 : x.asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime
    intro a ha
    rw [Ideal.mem_comap, hx0, Ideal.mem_bot] at ha
    have ha0 : a = 0 :=
      IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s))
        (by simpa using ha)
    rw [ha0]
    exact Ideal.zero_mem _
  have h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳
      hZ.1.genericPoint := by
    rw [Scheme.Hom.comp_apply, ← hp]
    exact hxp.map (S.fromSpecStalk s).continuous
  have h2 : hZ.1.genericPoint ⤳ j u := hg.specializes hu
  exact (h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTrace
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem traceOnLattice_eq_rank_mul_trace : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (a : Λ), (ρ a).trace = (N : ℤ_[p]) * Algebra.trace ℤ_[p] Λ a := by
  intro p _ Λ _ _ _ _ _ _ N h hh ρ a
  let f : Λ →+* Module.End ℤ_[p] (Fin h → ℤ_[p]) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin h) (Fin h) ℤ_[p] ≃ₐ[ℤ_[p]] _).toAlgHom.comp ρ).toRingHom
  letI : Module Λ (Fin h → ℤ_[p]) := Module.compHom _ f
  have hsmul : ∀ (b : Λ) (x : Fin h → ℤ_[p]), b • x = (ρ b).mulVec x := fun b x => rfl
  haveI : IsScalarTower ℤ_[p] Λ (Fin h → ℤ_[p]) := ⟨fun r b x => by
    rw [hsmul, hsmul, map_smul]
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]⟩
  haveI : Module.Finite Λ (Fin h → ℤ_[p]) := Module.Finite.of_restrictScalars_finite ℤ_[p] Λ _
  haveI : NoZeroSMulDivisors Λ (Fin h → ℤ_[p]) := ⟨fun {b x} hbx => by
    by_cases hb : b = 0
    · exact Or.inl hb
    · exact Or.inr (GlobalTheory.T.faithful_rep_mulVec_injective ℤ_[p] Λ h ρ b x hb (by rw [← hsmul]; exact hbx))⟩
  haveI : Module.Free Λ (Fin h → ℤ_[p]) := Module.free_of_finite_type_torsion_free'
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank Λ (Fin h → ℤ_[p]) = N := by
    have h1 := Module.finrank_mul_finrank ℤ_[p] Λ (Fin h → ℤ_[p])
    rw [Module.finrank_fin_fun] at h1
    have h2 := h1.trans hh
    have hpos : 0 < Module.finrank ℤ_[p] Λ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have key := GlobalTheory.T.trace_lsmul_eq_finrank_mul_trace ℤ_[p] Λ (Fin h → ℤ_[p]) a
  rw [hrank] at key
  rw [← key]
  have hlin : Algebra.lsmul ℤ_[p] ℤ_[p] (Fin h → ℤ_[p]) a = Matrix.toLin' (ρ a) := by
    exact LinearMap.ext fun x => hsmul a x
  rw [hlin, Matrix.trace_toLin'_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldFormallySmooth
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.residueField_formallySmooth_of_isClosed : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  intro k _ _ X f _ U x hxU _
  letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have key : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hS0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := by
    intro p
    have := StructureSheaf.IsLocalization.to_stalk k p
    have := Algebra.EssFiniteType.of_isLocalization (R := k)
      ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.essFiniteType_algebraMap.mpr this
  have hS : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType := hS0 (f x)
  have hT : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial =
      StructureSheaf.toStalk k (f x) := by
    rw [Scheme.ΓSpecIso_inv]
    exact StructureSheaf.toOpen_germ _ _ _
  have hφ : algebraMap k (X.presheaf.stalk x) =
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial) ≫
        f.stalkMap x).hom := by
    show ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, key]
  have hS' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Sp k).presheaf.germ ⊤ (f x) trivial).hom.EssFiniteType := hT ▸ hS
  have hR : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have hE : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))).EssFiniteType := by
    have h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
        (IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x)) := rfl
    rw [h, hφ, CommRingCat.hom_comp]
    exact (hS'.comp (LocallyOfFiniteType.stalkMap f x)).comp hR.essFiniteType
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.essFiniteType_algebraMap.mp hE
  exact Algebra.FormallySmooth.of_perfectField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem card_ringHom_to_integers_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    Finite (Λ →+* O) ∧ Nat.card (Λ →+* O) = Module.finrank ℤ_[p] Λ := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _
  letI : Algebra ℤ_[p] O := (padicToO p O).toAlgebra
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hZC : Function.Injective (algebraMap ℤ_[p] C) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    have hu : algebraMap ℤ_[p] C (PadicInt.unitCoeff h0 : ℤ_[p]) ≠ 0 :=
      ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero
    have hp : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact (mul_ne_zero hu (pow_ne_zero _ hp)) hx
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZC
  have hZE : Function.Injective (algebraMap ℤ_[p] (FractionRing Λ)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] Λ (FractionRing Λ)]
    exact (IsFractionRing.injective Λ (FractionRing Λ)).comp (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : FaithfulSMul ℤ_[p] (FractionRing Λ) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZE
  letI : Algebra (FractionRing ℤ_[p]) (FractionRing Λ) := FractionRing.liftAlgebra ℤ_[p] (FractionRing Λ)
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) (FractionRing Λ) :=
    FractionRing.isScalarTower_liftAlgebra ℤ_[p] (FractionRing Λ)
  letI : Algebra (FractionRing ℤ_[p]) C := FractionRing.liftAlgebra ℤ_[p] C
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) C := FractionRing.isScalarTower_liftAlgebra ℤ_[p] C
  have hrank : Module.finrank (FractionRing ℤ_[p]) (FractionRing Λ) = Module.finrank ℤ_[p] Λ :=
    IsFractionRing.finrank_eq ℤ_[p] (FractionRing ℤ_[p]) Λ (FractionRing Λ)
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  have hpos : 0 < Module.finrank ℤ_[p] Λ := Module.finrank_pos
  haveI : FiniteDimensional (FractionRing ℤ_[p]) (FractionRing Λ) :=
    Module.finite_of_finrank_pos (hrank ▸ hpos)
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing Λ) := inferInstance
  have hcard := AlgHom.card (FractionRing ℤ_[p]) (FractionRing Λ) C

  haveI : Algebra.IsIntegral ℤ_[p] Λ := Algebra.IsIntegral.of_finite ℤ_[p] Λ
  let Φ : (Λ →+* O) → (Λ →+* C) := fun σ => (algebraMap O C).comp σ
  have hΦ : Function.Injective Φ := fun σ τ h =>
    RingHom.ext fun x => hv.hom_inj (RingHom.congr_fun h x)
  let Ψ : (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) → (Λ →+* C) :=
    fun φ => (φ : FractionRing Λ →+* C).comp (algebraMap Λ (FractionRing Λ))
  have hΨ : Function.Injective Ψ := fun φ ψ h =>
    AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Λ) h)
  have hrange : Set.range Φ = Set.range Ψ := by
    ext τ
    constructor
    · rintro ⟨σ, rfl⟩
      have hcomm : ∀ c : ℤ_[p], Φ σ (algebraMap ℤ_[p] Λ c) = algebraMap ℤ_[p] C c := by
        intro c
        have hu := GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))
        have := RingHom.congr_fun hu c
        simp only [RingHom.comp_apply] at this
        change algebraMap O C (σ (algebraMap ℤ_[p] Λ c)) = algebraMap O C (padicToO p O c)
        rw [this]
      let τa : Λ →ₐ[ℤ_[p]] C := { Φ σ with commutes' := hcomm }
      have hinj : Function.Injective τa := by
        rw [injective_iff_map_eq_zero]
        have hk : RingHom.ker (τa : Λ →+* C) = ⊥ := by
          apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
          rw [eq_bot_iff]
          intro c hc
          rw [Ideal.mem_comap, RingHom.mem_ker] at hc
          have : algebraMap ℤ_[p] C c = 0 := by rw [← hc]; exact (τa.commutes c).symm
          rw [Ideal.mem_bot]
          exact hZC (by rw [this, map_zero])
        intro x hx
        have : x ∈ RingHom.ker (τa : Λ →+* C) := hx
        rwa [hk, Ideal.mem_bot] at this
      let φ0 : FractionRing Λ →ₐ[ℤ_[p]] C := IsFractionRing.liftAlgHom (K := FractionRing Λ) hinj
      refine ⟨φ0.extendScalarsOfIsLocalization (FractionRing ℤ_[p]) (nonZeroDivisors ℤ_[p]), ?_⟩
      ext x
      change φ0 (algebraMap Λ (FractionRing Λ) x) = τa x
      rw [IsFractionRing.liftAlgHom_apply]
      exact IsFractionRing.lift_algebraMap hinj x
    · rintro ⟨φ, rfl⟩
      let τa : Λ →ₐ[ℤ_[p]] C :=
        (φ.restrictScalars ℤ_[p]).comp (IsScalarTower.toAlgHom ℤ_[p] Λ (FractionRing Λ))
      have hmem : ∀ x : Λ, ∃ y : O, algebraMap O C y = τa x := by
        intro x
        have h1 : IsIntegral ℤ_[p] (τa x) := (Algebra.IsIntegral.isIntegral x).map τa
        have h2 : IsIntegral O (τa x) := h1.tower_top
        exact hv.exists_of_le_one (hv.mem_of_integral h2)
      let e : O ≃+* (algebraMap O C).range :=
        RingEquiv.ofBijective (algebraMap O C).rangeRestrict
          ⟨fun a b h => hv.hom_inj (congrArg Subtype.val h), (algebraMap O C).rangeRestrict_surjective⟩
      let σ : Λ →+* O := e.symm.toRingHom.comp ((τa : Λ →+* C).codRestrict (algebraMap O C).range
        (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩))
      refine ⟨σ, ?_⟩
      ext x
      have := congrArg Subtype.val (e.apply_symm_apply
        ((τa : Λ →+* C).codRestrict (algebraMap O C).range
          (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩) x))
      exact this
  let eqv : (Λ →+* O) ≃ (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) :=
    (Equiv.ofInjective Φ hΦ).trans ((Equiv.setCongr hrange).trans (Equiv.ofInjective Ψ hΨ).symm)
  refine ⟨Finite.of_equiv _ eqv.symm, ?_⟩
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, hcard, hrank]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumTraceEq
section
noncomputable section

open WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_actH_eq_trace_actT : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (a : Λ), (actH D a).trace = (actT D a).trace ∧ (actT D a).trace = padicToO p O (D.ρT a).trace := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D a
  obtain ⟨hdom, hmu⟩ := GlobalTheory.T.ainf_isDomain_mu_ne_zero p C v O hv ε hε
  haveI := hdom
  obtain ⟨-, -, htr⟩ := GlobalTheory.T.matrix_sandwich_trace_eq (Ainf p O) h (mu ε) D.F D.G
    ((D.ρT a).map (ofPadic p O)) (D.ρM a) hmu D.G_mul_F (D.F_act a)
  have hT : (actT D a).trace = fontaineTheta O p (((D.ρT a).map (ofPadic p O)).trace) := by
    simp only [actT, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, padicToO,
      RingHom.comp_apply]
  have hH : (actH D a).trace = fontaineTheta O p ((D.ρM a).trace) := by
    simp only [actH, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  refine ⟨by rw [hH, hT, htr], ?_⟩
  rw [hT]
  simp only [padicToO, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, RingHom.comp_apply]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerProductEuclideanModelsAgreeStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_product_euclidean_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  first | exact @GlobalTheory.Proof.schrodinger_models_agree | exact GlobalTheory.Proof.schrodinger_models_agree | (intros; apply GlobalTheory.Proof.schrodinger_models_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
section
open MeasureTheory Matrix

namespace GlobalTheory
open ValuativeRel

theorem norm_addChar_nonarch {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (t : k) : ‖ψ0 t‖ = 1 := by
  have hO : IsCompact (𝒪[k] : Set k) := by exact GlobalTheory.SplitWeil.Model.isCompact_int
  have hK : IsCompact ((fun u => t * u) '' (𝒪[k] : Set k)) := hO.image (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := (hK.image hψ).isBounded.exists_norm_le
  have hpow : ∀ n : ℤ, ‖ψ0 t‖ ^ n ≤ C := fun n => by
    have hmem : ψ0 (t * (n : k)) ∈ ψ0 '' ((fun u => t * u) '' (𝒪[k] : Set k)) :=
      ⟨t * n, ⟨n, intCast_mem _ n, rfl⟩, rfl⟩
    have := hC _ hmem
    rwa [mul_comm, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow, norm_zpow] at this
  have hne : ψ0 t ≠ 0 := fun h => by
    have := AddChar.map_add_eq_mul ψ0 t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hpos : 0 < ‖ψ0 t‖ := norm_pos_iff.2 hne
  refine le_antisymm ?_ ?_
  · by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hpow n) (by rw [zpow_natCast]; exact not_le.2 hn)
  · by_contra h
    have h1 : 1 < ‖ψ0 t‖⁻¹ := one_lt_inv₀ hpos |>.2 (not_le.1 h)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h1
    have := hpow (-(n : ℤ))
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    exact absurd this (not_le.2 hn)

theorem schr_unitary : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  intro k _ _ _ _ _ ψ0 hψ κ _ μ hμ w φ φ'
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have h1 : ∀ s : k, ψ0 s * (starRingEnd ℂ) (ψ0 s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar_nonarch ψ0 hψ s]; simp
  have h2 : (fun y => GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y)) =
      fun y => φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1)) := by
    funext y
    simp only [GlobalTheory.WeilM.schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))
    linear_combination (φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1))) * this
  rw [h2]
  exact integral_add_right_eq_self (fun y => φ y * (starRingEnd ℂ) (φ' y)) w.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVecStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm → (∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) → ∀ x : EuclideanSpace ℝ l, f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec <;> assumption)
end

