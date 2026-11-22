import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PxIsCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinLamOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ComponentsGoodRankTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL3
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.AbsGood
section
theorem UpperTheory.V.J.absGood :
    UpperTheory.V.J.AbsGood := by
  intro l _ O _ _ _ _ _ F T₂ T₃ J₂ J₃ h₂ h₃
  obtain ⟨φ₂, hφ₂, hs₂⟩ := UpperTheory.V.Pr.phiEx l O F 2 T₂
  obtain ⟨φ₃, hφ₃, hs₃⟩ := UpperTheory.V.Pr.phiEx l O F 3 T₃
  obtain ⟨Λ₂, hΛ₂⟩ := h₂.fin
  obtain ⟨Λ₃, hΛ₃⟩ := h₃.fin
  have good₂ : UpperTheory.V.Pr.AllGood T₂.S (Ideal.map φ₂ J₂) :=
    UpperTheory.V.Pr.components_good_rank_two l O F T₂.C₀ T₂.ok T₂.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂)
      (UpperTheory.V.Pr.p1Of l O F 2 T₂ φ₂ hφ₂ h₂.n4 J₂ h₂.p1)
      (UpperTheory.V.Pr.seedOf l O F 2 T₂ φ₂ hφ₂ J₂ h₂.unr h₂.dim h₂.seed)
  refine ⟨φ₃, hφ₃, hs₃, ?_⟩
  exact (UpperTheory.V.Pr.components_good_rank_three l O F T₃.C₀ T₃.ok T₃.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂) good₂
      T₃.S (Ideal.map φ₃ J₃)
      (UpperTheory.V.Pr.finLamOf l O F 3 T₃ φ₃ hφ₃ hs₃ Λ₃ J₃ hΛ₃)
      (UpperTheory.V.Pr.p1Of l O F 3 T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p1)
      (UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition l O F T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p3)
      (UpperTheory.V.Pr.seedOf l O F 3 T₃ φ₃ hφ₃ J₃ h₃.unr h₃.dim h₃.seed)).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IrrOpen
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N

namespace UpperTheory.V.J

section Abstract

private theorem tr_comap' {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G) (g : H) :
    (D.comap φ).tr (MonoidAlgebra.single g 1) = D.tr (MonoidAlgebra.single (φ g) 1) := by
  have hc : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
        (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single g 1))) = _
    congr 1
    rw [map_sub]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [GDet.tr, GDet.lam, hc]

private theorem tr_at {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
    (h : (D.map f).comap φ = GDet.ofRep ρ) (g : H) :
    f (D.tr (MonoidAlgebra.single (φ g) 1)) = (ρ g).trace := by
  have h1 : f (D.tr (MonoidAlgebra.single (φ g) 1)) = (D.map f).tr (MonoidAlgebra.single (φ g) 1) := by
    have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single (φ g) 1)).2 1
    simpa [GDet.tr, MonoidAlgebra.mapRingHom_apply] using this.symm
  rw [h1, ← tr_comap', h, ← (UpperTheory.V.CA.d_toDet _ _).2.2.1, (UpperTheory.V.CA.d_toDet_ofRep).1 ρ,
    (UpperTheory.V.CA.d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
  congr 1

private theorem gram_at {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
    (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
    f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
      Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [tr_at hn D f φ ρ h, map_mul]

private theorem isIrr_iff_span {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n)
    (r : Γ →* GL (Fin n) k) : IsIrr r ↔ Submodule.span k (Set.range (mat r)) = ⊤ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
  constructor
  · intro h N hN
    obtain ⟨-, -, h3⟩ := h
    exact h3 N le_top fun g v hv => hN g v hv
  · intro h
    refine ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun W _ hW => h W fun g v hv => hW g v hv⟩

end Abstract

end UpperTheory.V.J

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IsLiftMap
section
noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.J

section Lift

variable {O R C : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [CommRing C] [Algebra O C] [IsCO O C]

private theorem map_max_le (f : R →ₐ[O] C) :
    (maximalIdeal R).map (f : R →+* C) ≤ maximalIdeal C := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show f a ∈ maximalIdeal C
  rw [← res_eq_zero_iff O C, res_map, res_eq_zero_iff]
  exact ha

private theorem adic_map {Γ : Type} [TopologicalSpace Γ] (f : R →ₐ[O] C) {u : Γ → R}
    (hu : AdicCont (maximalIdeal R) u) : AdicCont (maximalIdeal C) fun g => f (u g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal C ^ N).comap (f : R →+* C) := by
    refine Ideal.map_le_iff_le_comap.1 ?_
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_max_le f) N
  exact (hu N).comp (Ideal.quotientMap (maximalIdeal C ^ N) (f : R →+* C) hle)

variable {l : ℕ} [Fact l.Prime] {F : Frame l (ResidueField O)} {n : ℕ}

private theorem isLift_map (f : R →ₐ[O] C) {ρ : NRep F n R} (h : UpperTheory.V.Fr.IsLift O ρ) :
    UpperTheory.V.Fr.IsLift O (ρ.map (f : R →+* C)) := by
  obtain ⟨hc, hb, hd⟩ := h
  have hres : ((res O C : C →ₐ[O] ResidueField O) : C →+* ResidueField O).comp (f : R →+* C) =
      ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) := by
    ext x
    exact res_map f x
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adic_map f (hc.1 i j)
  · exact adic_map f (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

end Lift

theorem det : Det := by
  intro l _ O _ _ _ _ F n S ξ D hD hr hψ
  haveI hc : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  haveI hn : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsCO O O := IsCO.self O
  haveI : IsCO O (TrivSqZeroExt O O) := co_sqz O O O (fun c => rfl)
  obtain ⟨y, hy⟩ := (der_hom O S.R O O ξ D).1 ⟨D, hD, rfl⟩
  let z : S.R →ₐ[O] TrivSqZeroExt O O := (TrivSqZeroExt.inlAlgHom O O O).comp ξ
  have key : ∀ a : S.R, D a = 0 → y a = z a := fun a ha =>
    TrivSqZeroExt.ext (hy a).1 (by rw [(hy a).2, ha]; rfl)
  have hmap : NRep.map (y : S.R →+* TrivSqZeroExt O O) S.ρ =
      NRep.map (z : S.R →+* TrivSqZeroExt O O) S.ρ := by
    apply NRep.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact key _ (hr g i j)
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      exact key _ (hψ v i g)
  obtain ⟨f, _, huniq⟩ := S.univ (TrivSqZeroExt O O) _ (isLift_map z S.lift)
  have e : y = z := (huniq y hmap).trans (huniq z rfl).symm
  ext a
  have h2 := (hy a).2
  rw [e] at h2
  rw [← h2]
  rfl

end UpperTheory.V.J

end
end

