import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0734
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0131
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def incl (d : ℕ) : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] (Fin d → ℚ_[l]) :=
  (Algebra.linearMap ℤ_[l] ℚ_[l]).compLeft (Fin d)

theorem incl_apply (d : ℕ) (v : Fin d → ℤ_[l]) : incl d v = fun i => algebraMap ℤ_[l] ℚ_[l] (v i) := rfl

theorem incl_injective (d : ℕ) : Function.Injective (incl (l := l) d) := by
  intro v w h
  funext i
  have := congrFun h i
  simp only [incl_apply] at this
  exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) this

theorem qRep_incl {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) (v : Fin d → ℤ_[l]) :
    qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v) := by
  funext i
  change (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ (fun j => algebraMap ℤ_[l] ℚ_[l] (v j))) i = algebraMap ℤ_[l] ℚ_[l] (((ρ g).val *ᵥ v) i)
  rw [RingHom.map_mulVec]
  rfl

end GlobalTheory.BKLim.StdLat

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def lat {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Formalism.WeaklyAdmissibleFiltrations.Lattice (LL := ℚ_[l]) (O := ℤ_[l]) (V := Fin d → ℚ_[l]) (qRep ρ) where
  T := LinearMap.range (incl d)
  stable g x hx := by
    obtain ⟨v, rfl⟩ := hx
    exact ⟨_, (qRep_incl ρ g v).symm⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (incl d) (incl_injective d))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨Pi.single j 1, ?_⟩
    funext i
    simp [incl_apply, Pi.single_apply]

noncomputable def equiv {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    (Fin d → ℤ_[l]) ≃ₗ[ℤ_[l]] ↥(lat ρ).T :=
  LinearEquiv.ofInjective (incl d) (incl_injective d)

theorem equiv_apply {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (v : Fin d → ℤ_[l]) :
    ((equiv ρ v : ↥(lat ρ).T) : Fin d → ℚ_[l]) = incl d v := rfl

noncomputable def basis {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Module.Basis (Fin d) ℤ_[l] ↥(lat ρ).T :=
  (Pi.basisFun ℤ_[l] (Fin d)).map (equiv ρ)

theorem toMatrix_act {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (basis ρ) (basis ρ) (actT (lat ρ) g) = (ρ g).val := by
  have key : ∀ v, (equiv ρ).symm (actT (lat ρ) g (equiv ρ v)) = (ρ g).val *ᵥ v := by
    intro v
    apply (equiv ρ).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [equiv_apply]
    change qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v)
    exact qRep_incl ρ g v
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, key,
    Pi.basisFun_apply, Pi.basisFun_repr]
  simp [Matrix.mulVec_single]

theorem cont_act {d : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin d) ℤ_[l]) (hρ : Continuous ρ)
    (x : Fin d → ℚ_[l]) : Continuous fun g => qRep ρ g x := by
  have h1 : Continuous fun g => ((ρ g).val : Matrix (Fin d) (Fin d) ℤ_[l]) := Units.continuous_val.comp hρ
  have h2 : Continuous fun g => ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) :=
    h1.matrix_map (continuous_subtype_val)
  exact h2.matrix_mulVec continuous_const

end GlobalTheory.BKLim.StdLat

theorem GlobalTheory.BKLim.crys_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsCrys (P.PD K) (qRep ρ) → Nonempty (Seed bk d (fun g => (ρ g).val) τ) := by
  intro l _ K bk τ hτ P AI T d ρ hρc hc
  have h := GlobalTheory.SeedExists.exists_seed l K bk τ hτ P AI ⟨T⟩ (Fin d → ℚ_[l]) (qRep ρ) (GlobalTheory.BKLim.StdLat.lat ρ)
    (GlobalTheory.BKLim.StdLat.cont_act ρ hρc) hc d (GlobalTheory.BKLim.StdLat.basis ρ)
  simp only [GlobalTheory.BKLim.StdLat.toMatrix_act] at h
  exact h

theorem GlobalTheory.BKLim.exists_frame_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsSst P (qRep ρ) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∃ F : Frame bk N d fun g => (ρ g).val, F.IsDR ∧ (IsCrys (P.PD K) (qRep ρ) → F.IsCr) := by
  intro l _ K bk τ hτ P AI T N d ρ hρc hsst hjump
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinv := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  have hdr : IsDR (P.PD K) (qRep ρ) := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  have hHN := hH N hjump
  have hunit : ∀ g, IsUnit ((ρ g).val) := fun g => (ρ g).isUnit
  obtain ⟨s, hs⟩ : ∃ s : WSeed bk d (fun g => (ρ g).val) τ, IsCrys (P.PD K) (qRep ρ) → ∀ g, s.κ g = 1 := by
    by_cases hc : IsCrys (P.PD K) (qRep ρ)
    · obtain ⟨sd⟩ := GlobalTheory.BKLim.crys_seed l K bk τ hτ P AI T d ρ hρc hc
      obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_trivial_cocycle_crystalline_period_data l K bk τ hτ d _ sd
      exact ⟨s', fun _ => hs'⟩
    · obtain ⟨N', c₁, c₂, c₃, k₀, F, F', X, X', Z, Z', κ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        GlobalTheory.T.exists_semistable_lattice_periods_acris l K bk P AI T C hC d ρ hsst
      obtain ⟨s⟩ := GlobalTheory.T.semistableSeed_of_acris_periods l K bk C τ hτ d (fun g => (ρ g).val) N' c₁ c₂ c₃ k₀ F F' X X' Z Z' κ
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨s, fun h => absurd h hc⟩
  obtain ⟨N', F, hFdr, hFcr⟩ := GlobalTheory.T.exists_breuilKisinFrame_semistablePeriods l K bk τ hτ d _ hunit s
  obtain ⟨F₀, -, hε⟩ := GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le l K bk τ hτ C hinv.2 N' N d _ F hFdr H hHN
  refine ⟨F₀, ?_, fun hc => ?_⟩
  · unfold Frame.IsDR Frame.IsBeta at hFdr ⊢
    rw [hε]; exact hFdr
  · have := hFcr (hs hc)
    unfold Frame.IsCr at this ⊢
    rw [hε]; exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePartMulDefiniteUnitaryInfinitePoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RatFinPart

theorem exists_gq_mul_infU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) :
    ∀ γ ∈ ratU L n, ∃ (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom ∧
      γ * (F.j γQ)⁻¹ ∈ infU L n := by
  intro γ hγ
  obtain ⟨γ₀, hγ₀⟩ := (Subgroup.mem_subgroupOf).1 hγ
  set σ : L →+* L := (IsCMField.complexConj L : L →+* L) with hσ
  have hU := γ.2
  change Formalism.UG.cT (conjAd L) ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
    ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1 at hU
  rw [← hγ₀] at hU
  have h2 : Matrix.transpose ((γ₀ : Matrix (Fin n) (Fin n) L).map σ) * (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := by
    have hinj : Function.Injective (algebraMap L (Ad L)) := fun x y h => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
      have := congrArg (fun z => pInf L z w) h
      simp only [pInf_algebraMap] at this
      exact w.embedding.injective this
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hU, Matrix.mul_one]
    congr 1
    ext i j
    simp [Formalism.UG.cT, ratGL, conjAd_algebraMap, hσ]
  have hu : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT σ γ₀ = 1 := mul_eq_one_comm.1 h2
  let g : GL (Fin n) (AL L) := Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀
  have hcj : ∀ x : L, conjAL L (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) =
      σ x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) := fun x => rfl
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := by
    change (g : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = 1
    have e : conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) =
        (conjT σ (γ₀ : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom := by
      ext i j
      simp [conjT, g, hcj]
    rw [e]
    change (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom * _ = 1
    rw [← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : (⟨g, hg⟩ : ReciprocityTheory.Aut.GA L n) ∈ GQ L n := by
    rw [GQ, Subgroup.mem_subgroupOf]
    exact ⟨γ₀, hu, rfl⟩
  let x : GAf L n := ⟨g, hg⟩
  refine ⟨⟨x, hq⟩, γ₀, hγ₀.symm, rfl, ?_⟩
  rw [infU, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  ext s t : 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hl := F.loc x w s t
  have e1 : (cLoc w (F.j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w := rfl
  change pFin L ((γ.1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w =
    pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w
  rw [← e1, hl, ← hγ₀]
  change pFin L (algebraMap L (Ad L) ((γ₀ : Matrix (Fin n) (Fin n) L) s t)) w =
    F.κ ((γ₀ : Matrix (Fin n) (Fin n) L) s t ⊗ₜ 1) w
  rw [F.left]
  rfl

end GlobalTheory.RatFinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpper
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HwUpper

theorem telescope (d : ℕ → ℂ) (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (m : ℕ) :
    (∏ s ∈ Finset.range m, (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) *
      (∏ k ∈ Finset.range m, d k) ^ f m = ∏ k ∈ Finset.range m, d k ^ f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ (fun k => d k ^ f k), ← ih, mul_assoc, mul_assoc]
    congr 1
    rw [← pow_add, Nat.sub_add_cancel (hf m), Finset.prod_range_succ, mul_pow]

theorem hwScal_transpose {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (B : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.BasicNotions.Examples₂.NZ.hwScal ℂ (le_refl n) ν B.transpose = ∏ i, B i i ^ ν i := by
  classical
  set d : ℕ → ℂ := fun k => if h : k < n then B ⟨k, h⟩ ⟨k, h⟩ else 1 with hd
  set f : ℕ → ℕ := fun k => if h : k < n then ν ⟨k, h⟩ else 0 with hfd
  have hf : ∀ s, f (s + 1) ≤ f s := by
    intro s
    by_cases h : s + 1 < n
    · simp only [hfd, dif_pos h, dif_pos (show s < n by omega)]
      exact hν (show (⟨s, by omega⟩ : Fin n) ≤ ⟨s + 1, h⟩ from Fin.mk_le_mk.mpr (by omega))
    · simp only [hfd, dif_neg h]
      exact Nat.zero_le _
  have hinner : ∀ s : Fin n, (∏ a : Fin (s.val + 1),
      B.transpose (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) = ∏ k ∈ Finset.range (s.val + 1), d k := by
    intro s
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun a _ => ?_
    have ha : a.val < n := by omega
    simp only [hd, dif_pos ha, Matrix.transpose_apply]
    rfl
  have hexp : ∀ s : Fin n, ν s - Formalism.GradedWeylDivisibility.nuNext ν s = f s.val - f (s.val + 1) := by
    intro s
    simp only [hfd, dif_pos s.2, Formalism.GradedWeylDivisibility.nuNext]
  unfold Formalism.BasicNotions.Examples₂.NZ.hwScal
  simp_rw [hinner, hexp]
  rw [Fin.prod_univ_eq_prod_range (fun s => (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) n]
  have hfn : f n = 0 := by simp [hfd]
  have ht := telescope d f hf n
  rw [hfn, pow_zero, mul_one] at ht
  rw [ht, ← Fin.prod_univ_eq_prod_range (fun k => d k ^ f k) n]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [hd, hfd, dif_pos i.2]

theorem exists_hw_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧
    ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  intro n lam
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨⟨extremal ℂ n lam, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩, fun h =>
    Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW (congrArg Subtype.val h), fun B hB => ?_⟩
  apply Subtype.ext
  set M : Matrix (Fin n) (Fin n) ℂ := (B : Matrix (Fin n) (Fin n) ℂ) with hM
  have hl : ∀ i j : Fin n, i < j → M.transpose i j = 0 := fun i j hij => by
    rw [Matrix.transpose_apply]; exact hB hij
  have hdet : M.det = ∏ i, M i i := Matrix.det_of_upperTriangular hB
  have hne : ∀ i, M i i ≠ 0 := by
    have h0 : M.det ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det B).ne_zero
      simpa [hM] using this
    rw [hdet, Finset.prod_ne_zero_iff] at h0
    exact fun i => h0 i (Finset.mem_univ i)
  have hw_eq : ∀ i, (lam.natW i : ℤ) + lam.detShift = lam.w i := by
    intro i
    have hle : lam.detShift ≤ lam.w i := by
      unfold DomWeight.detShift
      have hn : 0 < n := Fin.pos i
      rw [dif_pos hn]
      exact lam.anti (Fin.mk_le_mk.mpr (by omega) : i ≤ ⟨n - 1, by omega⟩)
    simp only [DomWeight.natW]
    omega
  rw [GlobalTheory.Branching.sqRep_coe, Submodule.coe_smul]
  show detPow ℂ n B lam.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M.transpose (extremal ℂ n lam) = _
  unfold extremal
  rw [Formalism.BasicNotions.Examples₂.NZ.rowAct_hw ℂ le_rfl lam.natW M.transpose hl, hwScal_transpose lam.natW ha M, smul_smul]
  congr 1
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← hM, hdet, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_add₀ (hne i), add_comm, hw_eq]

end GlobalTheory.HwUpper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumGiven

open scoped TensorProduct

theorem continuous_of_valued_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_inertDatum_of : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  intro L _ _ _ n v w hov hu hns s ϖ hs hU
  classical
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : s = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (continuous_of_valued_eq s hU.2.1)
      (continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  subst hsc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, s, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      s (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumGiven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalExtField

theorem exists_localExt_of_finiteIndex : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  intro E Ω _ _ _ _ _ A w h H hH hO
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_fixing_le_finiteIndex_weilSubgroup E Ω A w h (GlobalTheory.T.exists_pos_pow_galois_fixing_finset E Ω) (GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree E Ω A w h) (GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup E Ω A) H hH hO
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_primitive_element_stabilizer_finset E Ω s
  have hyH : ∀ σ : Weil h, (σ : G E Ω) y = y → σ ∈ H := fun σ hσ => hs σ ((hy σ).1 hσ)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit E Ω (H.map (Weil h).subtype) y
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_primitive_element_stabilizer_finset E Ω s'
  have hβH : ∀ σ : Weil h, (σ : G E Ω) β = β ↔ σ ∈ H := by
    intro σ
    rw [hβ, hs']
    constructor
    · intro hσ
      obtain ⟨τ', hτ', e⟩ := hσ 1 (one_mem _)
      obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ'
      have e1 : (σ : G E Ω) y = (τ₀ : G E Ω) y := by simpa using e
      have h2 : (τ₀⁻¹ * σ : Weil h) ∈ H := by
        apply hyH
        rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, e1, ← AlgEquiv.mul_apply,
          inv_mul_cancel, AlgEquiv.one_apply]
      simpa using H.mul_mem hτ₀ h2
    · intro hσ τ hτ
      refine ⟨(σ : G E Ω) * τ, Subgroup.mul_mem _ (Subgroup.mem_map_of_mem _ hσ) hτ, ?_⟩
      rfl
  obtain ⟨S, hS, f, hfm, hfdeg, hfinv, hfβ⟩ := GlobalTheory.LocalExtField.dorbit E Ω A β
  obtain ⟨r, hr0, hr⟩ : ∃ r : Ω, r ≠ 0 ∧ ∀ d ∈ Dec (F := E) A, d β ≠ β →
      A.valuation r ≤ A.valuation (d β - β) := by
    by_cases hne : (S.erase β).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (S.erase β).exists_min_image (fun x => A.valuation (x - β)) hne
      exact ⟨x - β, sub_ne_zero.mpr (Finset.ne_of_mem_erase hx), fun d hd hdβ =>
        hmin _ (Finset.mem_erase.mpr ⟨hdβ, (hS _).mpr ⟨d, hd, rfl⟩⟩)⟩
    · exact ⟨1, one_ne_zero, fun d hd hdβ =>
        absurd ⟨d β, Finset.mem_erase.mpr ⟨hdβ, (hS _).mpr ⟨d, hd, rfl⟩⟩⟩ hne⟩
  obtain ⟨g, hgm, hgdeg, β', hβ'g, hβ'⟩ :=
    GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition E Ω A (GlobalTheory.T.exists_base_near_of_decomposition_fixed E Ω A w h) f hfm hfinv β hfβ r hr0
  have hkr := GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version E Ω A β β' (fun d hd hdβ => lt_of_lt_of_le hβ' (hr d hd hdβ))
  obtain ⟨hall, hback⟩ := GlobalTheory.T.decompositionGroup_orbit_root_same_stabilizer E Ω A β β' S hS g hgm (hgdeg.trans hfdeg) hβ'g hkr
  have hint : IsIntegral E β' := Algebra.IsIntegral.isIntegral β'
  have agree : ∀ σ τ : G E Ω, σ β' = τ β' → ∀ x ∈ IntermediateField.adjoin E {β'}, σ x = τ x := by
    intro σ τ e x hx
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
    exact (AlgHom.eqOn_adjoin_iff (φ := (σ : Ω →ₐ[E] Ω)) (ψ := (τ : Ω →ₐ[E] Ω))).2
      (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact e) hx
  refine ⟨IntermediateField.adjoin E {β'}, IntermediateField.adjoin.finiteDimensional hint, ?_, ?_⟩
  · intro σ
    obtain ⟨d, hd, hσd⟩ := hall σ
    obtain ⟨τ, hτ, hτd⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h d hd β'
    exact ⟨⟨τ, hτ⟩, fun x => agree τ σ (hτd.trans hσd.symm) x x.2⟩
  · intro σ
    rw [← hβH σ]
    constructor
    · intro hσβ x
      have hσβ' := hback σ (Weil_le_Dec h σ.2) hσβ
      exact agree σ 1 (by simpa using hσβ') x x.2
    · intro hfix
      exact hkr σ (Weil_le_Dec h σ.2) (hfix ⟨β', IntermediateField.mem_adjoin_simple_self E β'⟩)

end GlobalTheory.LocalExtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  first | exact @GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span | exact GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span | (intros; apply GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  first | exact @GlobalTheory.BaseLiftWeight.lam_eq | exact GlobalTheory.BaseLiftWeight.lam_eq | (intros; apply GlobalTheory.BaseLiftWeight.lam_eq <;> assumption)
end

