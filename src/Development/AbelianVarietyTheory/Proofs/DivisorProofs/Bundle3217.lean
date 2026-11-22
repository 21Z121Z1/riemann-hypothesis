import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3188
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyUniformizationExists
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyFormGroupToPadicPointsComponent
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

open scoped Pointwise

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem kq_lc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    LocallyCompactSpace (KQ p K 1) ∧ SecondCountableTopology (KQ p K 1) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  let b := Module.finBasis ℚ_[p] (KQ p K 1)
  let e : KQ p K 1 ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] (KQ p K 1)) → ℚ_[p]) :=
    b.equivFun.toContinuousLinearEquiv
  exact ⟨e.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    e.toHomeomorph.isEmbedding.secondCountableTopology⟩

theorem isCompact_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    IsCompact (intKQ p K 1 : Set (KQ p K 1)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  obtain ⟨ι, _, b, hb⟩ := GlobalTheory.IntBasisKQ.exists_basis_intKQ p K inferInstance 1 one_pos
  let e : KQ p K 1 ≃L[ℚ_[p]] (ι → ℚ_[p]) := b.equivFun.toContinuousLinearEquiv
  have hset : (intKQ p K 1 : Set (KQ p K 1)) = e ⁻¹' Set.univ.pi fun _ => Metric.closedBall (0 : ℚ_[p]) 1 := by
    ext x
    simp only [SetLike.mem_coe, hb, Set.mem_preimage, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
    rfl
  rw [hset]
  exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)

theorem isCompact_Kres (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (n : ℕ) :
    IsCompact (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  set B : Set (Matrix (Fin n) (Fin n) (KQ p K 1)) := {M | ∀ i j, M i j ∈ intKQ p K 1} with hB
  have hBc : IsCompact B := by
    have : B = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (intKQ p K 1 : Set (KQ p K 1)) := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intKQ K
  have hB' : IsCompact (MulOpposite.unop ⁻¹' B : Set (Matrix (Fin n) (Fin n) (KQ p K 1))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hBc
  have e : (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) = Units.embedProduct _ ⁻¹' (B ×ˢ (MulOpposite.unop ⁻¹' B)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kres_iff, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      MulOpposite.unop_op, hB, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hBc.prod hB')

open Polynomial in

theorem rho_charpoly_sep (G : HTGroup p) (w : Fin G.m) (y : G.C) (hdeg : (minpoly G.F y).natDegree = G.n)
    (hsep : (minpoly G.F y).Separable) : (G.rho w y).charpoly.Separable := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  let ρF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    { G.rho w with
      commutes' := fun x => by
        change G.rho w (algebraMap G.F G.C x) = _
        rw [G.rho_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
          RingHom.algebraMap_toAlgebra, HTGroup.embW] }
  have hρF : ∀ c, ρF c = G.rho w c := fun _ => rfl
  let Φ : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) ρF (fun _ _ => Algebra.commute_algebraMap_left _ _)
  have hΦinj : Function.Injective Φ :=
    (Φ : G.Fw w ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) (G.Fw w)).injective
  set z : G.Fw w ⊗[G.F] G.C := (1 : G.Fw w) ⊗ₜ y with hz
  have hΦz : Φ z = G.rho w y := by
    change Φ ((1 : G.Fw w) ⊗ₜ y) = _
    refine (Algebra.TensorProduct.lift_tmul (Algebra.ofId (G.Fw w) (Matrix (Fin G.n) (Fin G.n) (G.Fw w))) ρF _
      (1 : G.Fw w) y).trans ?_
    rw [map_one, one_mul]
    exact hρF y
  set M := G.rho w y with hM
  have hliF : LinearIndependent G.F (fun i : Fin G.n => y ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := G.F) y
    rw [hdeg] at h
    exact h
  have hliC : LinearIndependent (G.Fw w) (fun i : Fin G.n => z ^ (i : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := G.Fw w) hliF
    convert h using 1
    funext i
    simp [z, Algebra.TensorProduct.tmul_pow]
  have hMint : IsIntegral (G.Fw w) M := Algebra.IsIntegral.isIntegral M
  have hQ0 : minpoly (G.Fw w) M ≠ 0 := minpoly.ne_zero hMint
  have hzQ : aeval z (minpoly (G.Fw w) M) = 0 := by
    apply hΦinj
    rw [map_zero, ← Polynomial.aeval_algHom_apply, hΦz, minpoly.aeval]
  have hdegQ : G.n ≤ (minpoly (G.Fw w) M).natDegree := by
    by_contra hlt
    push_neg at hlt
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at hzQ
    have hc := Fintype.linearIndependent_iff.1 hliC (fun i => (minpoly (G.Fw w) M).coeff i) hzQ
    apply hQ0
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < G.n
    · exact hc ⟨k, hk⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  set Pv := (minpoly G.F y).map (algebraMap G.F (G.Fw w)) with hPv
  have hPvM : aeval M Pv = 0 := by
    rw [hPv, Polynomial.aeval_map_algebraMap, hM, ← hρF, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hyint : IsIntegral G.F y := Algebra.IsIntegral.isIntegral y
  have hPvmon : Pv.Monic := (minpoly.monic hyint).map _
  have hPvdeg : Pv.natDegree = G.n := by
    rw [hPv, Polynomial.natDegree_map, hdeg]
  have hdvd : minpoly (G.Fw w) M ∣ Pv := minpoly.dvd (G.Fw w) M hPvM
  have hmin : minpoly (G.Fw w) M = Pv :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hMint) hPvmon hdvd (by omega)).symm
  have hchar : M.charpoly = Pv := by
    have h1 : minpoly (G.Fw w) M ∣ M.charpoly := Matrix.minpoly_dvd_charpoly M
    have h2 : M.charpoly.natDegree = G.n := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [hmin] at h1
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPvmon (Matrix.charpoly_monic M) h1
      (by omega)
  rw [hchar, hPv]
  exact hsep.map

theorem loc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {n : ℕ}
    (γ : GL (Fin n) (KQ p K 1)) (hγ : (γ : Matrix (Fin n) (Fin n) (KQ p K 1)).charpoly.Separable)
    (S₂ : Finset (GL (Fin n) (KQ p K 1))) :
    ∃ S : Finset (GL (Fin n) (KQ p K 1)), ∀ h : GL (Fin n) (KQ p K 1),
      (∃ s ∈ S₂, ∃ k₁ ∈ Kres p K n 1, ∃ k₂ ∈ Kres p K n 1, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : GL (Fin n) (KQ p K 1), a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ Kres p K n 1, h = a * s * k := by
  obtain ⟨hlc, hsc⟩ := kq_lc K
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  haveI : IsArtinianRing (KQ p K 1) := IsArtinianRing.of_finite ℚ_[p] (KQ p K 1)
  have hK := isCompact_Kres K n
  have hO := isOpen_Kres p K inferInstance n 1 one_pos
  set Ω : Set (GL (Fin n) (KQ p K 1)) := ⋃ s ∈ S₂,
    (fun x : GL (Fin n) (KQ p K 1) × GL (Fin n) (KQ p K 1) => x.1 * s * x.2) ''
      ((Kres p K n 1 : Set _) ×ˢ (Kres p K n 1 : Set _)) with hΩdef
  have hΩ : IsCompact Ω := S₂.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)
  obtain ⟨C, hC, hCx⟩ := GlobalTheory.Orb.isProperOrbit_GL (A := KQ p K 1) (g := γ) hγ Ω hΩ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun c : C => (c : GL (Fin n) (KQ p K 1)) • (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))))
    (fun c => hO.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_smul_set.2 ⟨1, one_mem _, by simp⟩⟩)
  refine ⟨t.image fun c : C => (c : GL (Fin n) (KQ p K 1)), fun h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ => ?_⟩
  have hmem : h⁻¹ * γ * h ∈ Ω := Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, he.symm⟩
  obtain ⟨u, hu, huC⟩ := hCx h hmem
  have := ht huC
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hx⟩ := this
  obtain ⟨k, hk, hck⟩ := Set.mem_smul_set.1 hx
  refine ⟨u⁻¹, ?_, c, Finset.mem_image_of_mem _ hc, k, hk, ?_⟩
  · have hu' : u * γ = γ * u := GlobalTheory.Orb.mem_cent.1 hu
    calc u⁻¹ * γ = u⁻¹ * (γ * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * γ) * u⁻¹ := by rw [hu']
      _ = γ * u⁻¹ := by group
  · have e : u * h = (c : GL (Fin n) (KQ p K 1)) * k := hck.symm
    calc h = u⁻¹ * (u * h) := by group
      _ = u⁻¹ * c * k := by rw [e]; group

end GlobalTheory.FinAtP

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem gl_one_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem prod_fin (G : HTGroup p) (γ : Gr G 1)
    (hγ : ∀ w, ((γ.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly.Separable)
    (S₂ : Finset (Gr G 1)) :
    ∃ S : Finset (Gr G 1), ∀ h : Gr G 1,
      (∃ s ∈ S₂, ∃ k₁ ∈ KHT p G.m G.n 1 G.Fw, ∃ k₂ ∈ KHT p G.m G.n 1 G.Fw, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : Gr G 1, a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ KHT p G.m G.n 1 G.Fw, h = a * s * k := by
  choose Sw hSw using fun w => loc (G.Fw w) (γ.2 w) (hγ w) (S₂.image fun s => s.2 w)
  refine ⟨(Fintype.piFinset Sw).image fun t => ((1 : GL (Fin 1) (Qr p 1)), t), ?_⟩
  rintro h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩
  have hw : ∀ w, ∃ a : GL (Fin G.n) (KQ p (G.Fw w) 1), a * γ.2 w = γ.2 w * a ∧
      ∃ s ∈ Sw w, ∃ k ∈ Kres p (G.Fw w) G.n 1, h.2 w = a * s * k := fun w =>
    hSw w (h.2 w) ⟨s.2 w, Finset.mem_image_of_mem _ hs, k₁.2 w, (Subgroup.mem_prod.1 hk₁).2 w (Set.mem_univ _),
      k₂.2 w, (Subgroup.mem_prod.1 hk₂).2 w (Set.mem_univ _), congrArg (fun x : Gr G 1 => x.2 w) he⟩
  choose a ha s' hs' k hk hk' using hw
  refine ⟨(h.1, a), Prod.ext (gl_one_comm _ _) (funext ha), (1, s'),
    Finset.mem_image.2 ⟨s', Fintype.mem_piFinset.2 hs', rfl⟩, (1, k),
    Subgroup.mem_prod.2 ⟨one_mem _, fun w _ => hk w⟩, Prod.ext (by simp) (funext fun w => ?_)⟩
  simp [hk' w]

theorem exists_finset_cosets {H : Type} [Group H] (K₀ K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) :
    ∃ T : Finset H, ∀ k ∈ K₀, ∃ t ∈ T, ∃ k' ∈ K, k = t * k' := by
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : H), fun k hk => ?_⟩
  set q : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K₀) ∈ K.subgroupOf K₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  refine ⟨((Quotient.out q : K₀) : H), Finset.mem_image_of_mem _ (Finset.mem_univ _), _, hq, ?_⟩
  simp

theorem charpoly_formGroupToPadicPoints_component (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : Fin G.m) :
    (((toP1 G β y).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly =
      (G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).charpoly.map (inclK p (G.Fw w) 1).toRingHom := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.FinAtP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinementStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForms_pullback_metric_flag_refinement : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  first | exact @GlobalTheory.ChernCalc.pullback_chernF | exact GlobalTheory.ChernCalc.pullback_chernF | (intros; apply GlobalTheory.ChernCalc.pullback_chernF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPartStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  first | exact @GlobalTheory.ChernCalc.chernTopPart_eq_part | exact GlobalTheory.ChernCalc.chernTopPart_eq_part | (intros; apply GlobalTheory.ChernCalc.chernTopPart_eq_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyUniformizationExistsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_variety_uniformization_exists : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
        ∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ)) := by
  first | exact @GlobalTheory.LatTorus.exists_unif_of_lattice | exact GlobalTheory.LatTorus.exists_unif_of_lattice | (intros; apply GlobalTheory.LatTorus.exists_unif_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqZeroOfEvAEqZeroOfLeFinrankStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (d q : ℕ) (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (J : Ideal A), Function.Surjective (MvPolynomial.aeval (R := K) x) → (∀ i, x i ^ q ∈ J) → q ^ d ≤ Module.finrank K (A ⧸ J) → ∀ f : MvPowerSeries (Fin d) K, evA K x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < q → coeff α f = 0 := by
  first | exact @GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank | exact GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank | (intros; apply GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtFubiniStudyLogSumWeight
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.CanSmooth

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_log {f : CxPts p σ → ℝ} (h : CInfAt f y) (hpos : 0 < f y) :
    CInfAt (fun z => Real.log (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hFy : 0 < F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds ▸ hpos
  refine ⟨W, ι, inferInstance, g, fun v => Real.log (F v), O ∩ F ⁻¹' Set.Ioi 0, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, hFy⟩,
    (h₄.mono Set.inter_subset_left).log fun v hv => (ne_of_gt hv.2), ?_⟩
  filter_upwards [h₅] with z hz
  rw [hz]

theorem cInfAt_sum {ι : Type} [DecidableEq ι] (s : Finset ι) {f : ι → CxPts p σ → ℝ}
    (h : ∀ l ∈ s, CInfAt (f l) y) : CInfAt (fun z => ∑ l ∈ s, f l z) y := by
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := p) (0 : ℝ) y
  | insert a s ha ih =>
    have e : (fun z => ∑ l ∈ insert a s, f l z) = fun z => f a z + ∑ l ∈ s, f l z :=
      funext fun z => Finset.sum_insert ha
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem cInfAt_normSq_ratVal [IsIntegral X] {g : X.functionField} (hg : RegAt (under y) g) :
    CInfAt (fun z : CxPts p σ => ‖ratVal g z‖ ^ 2) y := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hyU : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  have h₁ : CInfAt (fun z => ‖ev p σ U a z‖ ^ 2) y :=
    ⟨U, Unit, inferInstance, fun _ => a, fun v => ‖v ()‖ ^ 2, Set.univ, hyU, isOpen_univ, trivial,
      ((contDiff_apply ℝ ℂ ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
  refine h₁.congr ?_
  filter_upwards [(isOpen_ptsIn U).mem_nhds hyU] with z hz
  rw [ratVal_fnOf hz]

end GlobalTheory.HSAmp.CanSmooth

namespace GlobalTheory.HSAmp

open CanSmooth in

theorem cInfAt_canWeight : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), CInfAt (fun z : CxPts p σ => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ z (x l) ^ (2 * n))) y := by
  intro k _ X _ p P D e x hx n _ σ y
  set i := pick (P.L.φ σ).isLB y
  set j := pick (P.A.φ σ).isLB y
  have hi : y ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y
  have hφ : CInfAt ((P.L.φ σ).φ i) y := P.L.cInf σ i y hi
  have hterm : ∀ l, CInfAt (fun z => P.nu e 0 σ z (x l) ^ (2 * n)) y := by
    intro l
    have hreg : RegAt (under y) (P.loc e 0 (x l) i j) := hx.mem l _ i j (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h₂ := (cInfAt_normSq_ratVal hreg).comp₂ hφ
      (G := fun w => w.1 ^ n * Real.exp (-((e : ℝ) * n) * w.2))
      ((contDiff_fst.pow n).mul ((contDiff_const.mul contDiff_snd).exp))
    refine h₂.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hi, (isOpen_ptsIn _).mem_nhds hj] with z hzi hzj
    rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hzi hzj, mul_pow, pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsum : CInfAt (fun z => ∑ l, P.nu e 0 σ z (x l) ^ (2 * n)) y :=
    cInfAt_sum Finset.univ fun l _ => hterm l
  obtain ⟨l₀, hl₀⟩ := hx.cover (under y)
  have hpos₀ : 0 < P.nu e 0 σ y (x l₀) :=
    mul_pos (norm_pos_iff.2 (ratVal_ne_zero (hl₀ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)))) (Real.exp_pos _)
  have hpos : 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) :=
    lt_of_lt_of_le (pow_pos hpos₀ _)
      (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
        (fun l _ => (even_two_mul n).pow_nonneg _) (Finset.mem_univ l₀))
  exact (cInfAt_log hsum hpos).const_mul _

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLengthStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  first | exact @GlobalTheory.ChernCalc.cInfAt_logUnit_grD | exact GlobalTheory.ChernCalc.cInfAt_logUnit_grD | (intros; apply GlobalTheory.ChernCalc.cInfAt_logUnit_grD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentPointLastIndex
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FlatCore

namespace GlobalTheory.DefCoreLie

theorem frameDeg_def (hCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) [NeZero H.d] (χ : DirichletCharacter ℂ H.d) (hχ : GlobalTheory.IsKroneckerChar χ)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (hL : Laws U x) (hq : Dw.q = 0) : FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  intro Z τ s ρ hρ
  obtain ⟨K, iF, iN, iA, y, ρ₀, σ₁, X, t₀, hy, hm₁, hm₂, hρ₀⟩ := GlobalTheory.T.exists_cm_goodReduction_point_on_component E H Dw l Xo c r U x hL Z
  obtain ⟨F⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K X.B.pol
  obtain ⟨⟨h, hh⟩, -⟩ :=
    GlobalTheory.CM.LieMetric.exists_unique_isHerm GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 K X.B.pol F
  let f : 𝓞 E →+* K := (algebraMap c.F K).comp (embK c τ.1)
  have hf : ∀ a, IsIntegral ℤ (f a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map f.toIntAlgHom
  let t : 𝓞 E →+* 𝓞 K := f.codRestrict (integralClosure ℤ K).toSubring hf
  have ht : ∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a) := fun a => rfl
  obtain ⟨hfin, hdeg⟩ := GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy X.B t₀ hm₁ hm₂ F h hh t ht
  have htρ : t H.rt = ρ₀ := by
    apply RingOfIntegers.ext
    rw [ht, hρ₀ τ]
  exact ⟨hfin, hdeg.trans (hCM E H hH χ hχ K ρ₀ σ₁ Dw.p Dw.q X F h hh hq t htρ)⟩

end GlobalTheory.DefCoreLie

namespace GlobalTheory.DefCoreLie

theorem degLie_core : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hm hG hW hN hF Z P τ
  obtain ⟨hDC, -, -, -⟩ := GlobalTheory.T.deformation_case_finite_components p i PP A M hR hm hG hW hN hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  have hL : Laws (p.T.U ((i : ℕ) + 1)) (xiR D) := GlobalTheory.LawsCore.laws_core D p.T hJ _ hj hF
  obtain ⟨_, χ, hχ, hOm, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q hJ.pins.1 p.Del p.h0
  have hFr := frameDeg_def GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference D.host.E p.T.Q.H hH χ hχ _ _ _ _ _ _ _ hL hDC.q
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec (p.T.U ((i : ℕ) + 1)) (xiR D) hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ
  have h := (hFr Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
  rw [(GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s, s.deg_eq_toFrame, flatDegVal, ← hOm, ← h]
  rfl

end GlobalTheory.DefCoreLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  first | exact @GlobalTheory.GoodTop.isTopForm_mul_topDens | exact GlobalTheory.GoodTop.isTopForm_mul_topDens | (intros; apply GlobalTheory.GoodTop.isTopForm_mul_topDens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossRelationHomGivesExpansionTermConvolutionRelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crossRelation_hom_gives_expansionTerm_convolution_rel : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₁ : W0 U₁.toUnifPre) (w₂ : W0 U₂.toUnifPre), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') s₁ s₂ s₁' s₂', U₂.ExpandsF F j w₂ t₁ s₁ → U₂.ExpandsF F j w₂ t₂ s₂ → U₁.ExpandsF F j' w₁ t₁' s₁' → U₁.ExpandsF F j' w₁ t₂' s₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  first | exact @GlobalTheory.Mum.MixTwo.main | exact GlobalTheory.Mum.MixTwo.main | (intros; apply GlobalTheory.Mum.MixTwo.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCaseCuspFormFibreSlopeGeBoundStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteCase_cuspForm_fibre_slope_ge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ → ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  first | exact @GlobalTheory.DefFibre.fibreAt_defCase | exact GlobalTheory.DefFibre.fibreAt_defCase | (intros; apply GlobalTheory.DefFibre.fibreAt_defCase <;> assumption)
end

