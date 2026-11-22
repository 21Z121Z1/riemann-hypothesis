import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRationalMatrixCompatible
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hat_iff_swap {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h

theorem core {n r : ℕ} (h : n = r) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hF : Formalism.L2.DIV.IsFrame β Λ)
    (S K G : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (hSK : S * K = G * S)
    (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hk : k.val = K.map (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E))
    (hkS : k ∈ Formalism.L2.DIV.St β) (s A : Matrix (Fin r) (Fin r) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (hs : S = s.submatrix (Fin.cast h) (Fin.cast h)) (hA : G = A.submatrix (Fin.cast h) (Fin.cast h)) :
    ∀ y ∈ GlobalTheory.AdLat.hat F ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) :
        Set (Fin r → E)),
      ∃ y' ∈ GlobalTheory.AdLat.hat F ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) :
        Set (Fin r → E)), A *ᵥ (s *ᵥ y) = s *ᵥ y' := by
  subst h
  have e : Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast (rfl : n = n))) = Λ := by
    ext x
    simp only [Submodule.mem_comap, Fin.cast_refl]
    exact Iff.rfl
  simp only [Fin.cast_refl, submatrix_id_id] at hs hA
  subst hs hA
  rw [e]
  intro y hy
  refine ⟨K *ᵥ y, ?_, ?_⟩
  · rw [mem_hat_iff_swap] at hy ⊢
    have h1 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hkS _).1 hy
    convert h1 using 1
    funext i
    rw [hk]
    exact RingHom.map_mulVec (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingHom K y i
  · rw [mulVec_mulVec, mulVec_mulVec, hSK]

end General

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem inclAF_injective (D : D7) :
    Function.Injective (GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (E := D.host.E) (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mem_UJ_of_GQ (D : D7) (V : HSp D) (g : GA D V) (γ : GL (Fin V.rank) D.host.E) (hg : g ∈ GQ V)
    (hm : matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h1 : matHom V g ∈ GlobalTheoryTheory.GenusMassVolumes.HFin (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := hg
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 h1
  have e2 : Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) x =
      Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ := e.trans hm
  have : x = γ := by
    refine Units.ext (Matrix.ext fun a b => inclAF_injective D ?_)
    have := congrArg (fun M : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E) =>
      M.1 a b) e2
    simpa [Formalism.UG.bc] using this
  exact this ▸ hx

theorem finHom_val_of_mat (D : D7) (V : HSp D) (g : GA D V) (γ : GL (Fin V.rank) D.host.E)
    (hm : matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    (finHom V g).val = (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (fun x => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x) := by
  have : (finHom V g).val = ((matHom V g).val).map
      (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) := rfl
  rw [this, hm]
  ext a b
  simp [Formalism.UG.bc, GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

example (D : D7) (x : D.host.E) : letI : IsCMField D.host.E := D.host.isCMField_hostE;
    D.sp.cm.sig x = IsCMField.complexConj D.host.E x := rfl

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y =
      (fun b => (IsCMField.complexConj E : E →+* E) (y b)) ⬝ᵥ (J *ᵥ x) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  ring

theorem herm_unitary {n r : ℕ} (h : n = r) (J γ : Matrix (Fin n) (Fin n) E)
    (hγ : Formalism.UG.cT (IsCMField.complexConj E : E →+* E) γ * J * γ = J) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))ᵀ
        (γ.submatrix (Fin.cast h.symm) (Fin.cast h.symm) *ᵥ x) (γ.submatrix (Fin.cast h.symm) (Fin.cast h.symm) *ᵥ y) =
      ReciprocityTheory.ChartRestriction.G.FD.herm (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))ᵀ x y := by
  subst h
  simp only [Fin.cast_refl, submatrix_id_id]
  rw [herm_transpose, herm_transpose]
  have key : (fun b => (IsCMField.complexConj E : E →+* E) ((γ *ᵥ y) b)) =
      γ.map (IsCMField.complexConj E : E →+* E) *ᵥ (fun b => (IsCMField.complexConj E : E →+* E) (y b)) := by
    funext b
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [key, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, mulVec_mulVec, mulVec_mulVec]
  have hγ' : (γ.map (IsCMField.complexConj E : E →+* E))ᵀ * J * γ = J := hγ
  rw [hγ']

end Herm

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem fwd (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu) (hCl : Cl.Is t0) (i : Fin D.R.m)
    (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
    (hlift : ((finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)))
    (g : GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E)
    (hm : matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ)
    (hγr : (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E))
    (hk : Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) :
    ∀ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)),
      ∃ y' ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)),
        GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E) (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (s *ᵥ y) =
          s *ᵥ y' := by
  obtain ⟨c, hc⟩ := hCl.βW i
  set h := GlobalTheory.MassLink.lift D i s with hh
  have hSK : (finHom (Wc D i) h).val * (finHom (Wc D i) (h⁻¹ * g * h)).val =
      (finHom (Wc D i) g).val * (finHom (Wc D i) h).val := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have hA : (finHom (Wc D i) g).val = (GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E)
      (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)).submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) := by
    rw [finHom_val_of_mat D (Wc D i) g γ hm, ← hγr]
    ext a b
    simp [GlobalTheory.UCls.ratM]
  exact core (F := D.host.F) (rank_Wc i) (Cl.ΛW i) (Cl.βW i) hc.1 _ _ _ hSK
    (Formalism.IndefR.Lev.finE (Wc D i) (h⁻¹ * g * h)) rfl (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk)) s _
    hlift hA

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem ratStab_of_lift : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)),
    ((finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) →
    ∀ (g : GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E),
    g ∈ GQ (Wc D i) → matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
    (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) →
    (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 →
    Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) →
    γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  intro D Tu Cl t0 hCl i s hlift g γ γr hg hm hγr hdet hk
  refine ⟨hdet, fun x y => ?_, fun x => ?_⟩
  · have hU := mem_UJ_of_GQ D (Wc D i) g γ hg hm
    have := herm_unitary (rank_Wc i) (Wc D i).gram (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E)
      hU x y
    rw [hγr] at this
    exact this
  · have hm' : matHom (Wc D i) g⁻¹ = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ⁻¹ := by
      rw [map_inv, hm, map_inv]
    have hγr' : ((γ⁻¹ : GL (Fin (Wc D i).rank) D.host.E) : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix
        (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) =
        ((γr⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) := by
      rw [Matrix.coe_units_inv, Matrix.coe_units_inv, ← hγr]
      exact (Matrix.inv_submatrix_equiv _ (finCongr (rank_Wc i).symm) (finCongr (rank_Wc i).symm)).symm
    have hk' : Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g⁻¹ * GlobalTheory.MassLink.lift D i s) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) := by
      have e : (GlobalTheory.MassLink.lift D i s)⁻¹ * g⁻¹ * GlobalTheory.MassLink.lift D i s =
          ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s)⁻¹ := by group
      rw [e, map_inv]
      exact inv_mem hk
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨y', hy', e⟩ := fwd D Tu Cl t0 hCl i s hlift g⁻¹ γ⁻¹ γr⁻¹ hm' hγr' hk' y hy
      refine ⟨y', hy', ?_⟩
      rw [← e, hxy, mulVec_mulVec, ← GlobalTheory.SUVol.ratM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        GlobalTheory.SUVol.ratM_one, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨y', hy', e⟩ := fwd D Tu Cl t0 hCl i s hlift g γ γr hm hγr hk y hy
      exact ⟨y', hy', e.symm⟩

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem ratStab_mem : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)),
    GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s →
    ∀ (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E),
    g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
    (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) →
    (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 →
    Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) →
    γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  intro D Tu Cl t0 hCl i s hs
  exact ratStab_of_lift D Tu Cl t0 hCl i s (GlobalTheory.T.special_unitary_lift_in_theta_group D i s hs).2

end GlobalTheory.MassLink.StabLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surj_restrict_snd {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (Y : Over S)
    (V : Y.left.Opens) : Function.Surjective ((snd A Y).left ∣_ V).appTop.hom := by
  let T : Over S := Over.mk (V.ι ≫ Y.hom)
  let j : T ⟶ Y := Over.homMk V.ι rfl
  let m : (A ⊗ T).left ⟶ (A ⊗ Y).left := (lift (fst A T) (snd A T ≫ j)).left
  have hT : IsPullback (fst A T).left (snd A T).left A.hom (V.ι ≫ Y.hom) := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : m ≫ (fst A Y).left = (fst A T).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : m ≫ (snd A Y).left = (snd A T).left ≫ V.ι := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]; rfl
  have H : IsPullback m (snd A T).left (snd A Y).left V.ι :=
    IsPullback.of_right (by rw [m₁]; exact hT) m₂ hY
  let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict (snd A Y).left V) H.flip
  have he : e.hom ≫ (snd A T).left = (snd A Y).left ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hq : Function.Surjective (snd A T).left.appTop.hom := surj_snd GlobalTheory.SemiRigid.globalFns hA T
  have hi : Function.Surjective e.hom.appTop.hom := by
    have : IsIso (e.hom.app ⊤) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  rw [← he]
  exact surj_comp hi hq

theorem same_of_local : ∀ (S : Scheme.{0}) (A T U : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (Y : Over S) (y : Y ⟶ T) (u : Y ⟶ U),
    (∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      Same A N M (z ≫ y) (z ≫ u)) → Same A N M y u := by
  intro S A T U _ hA N M hN hM Y y u loc
  rw [same_iff hN.isLB hM.isLB]
  rw [← sub_eq_zero]
  obtain ⟨L, hL, hc⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hc, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 (CubeGlue.triv_of_locally_triv hL (snd A Y).left (lift 1 (𝟙 Y)).left ?_
    (surj_restrict_snd hA Y) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key]
    simp only [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  · intro p
    obtain ⟨Z, z, hz, ⟨q, hq⟩, hs⟩ := loc p
    refine ⟨z.left.opensRange, ⟨q, hq⟩, ?_⟩
    let V := (snd A Y).left ⁻¹ᵁ z.left.opensRange
    let X' : Over S := Over.mk (V.ι ≫ (A ⊗ Y).hom)
    let i : X' ⟶ A ⊗ Y := Over.homMk V.ι rfl
    have hr : Set.range (i ≫ snd A Y).left ⊆ Set.range z.left := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    let t : X' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ snd A Y).left hr) (by
      rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have ht : t ≫ z = i ≫ snd A Y := by
      ext1; exact IsOpenImmersion.lift_fac _ _ _
    rw [same_iff hN.isLB hM.isLB] at hs
    have e := congrArg (CechPic.pull (lift (i ≫ fst A Y) t).left) hs
    simp only [pull_evc, lift_fst, lift_snd_assoc] at e
    rw [← Category.assoc t z y, ← Category.assoc t z u, ht, Category.assoc, Category.assoc] at e
    show Triv (L.pull i.left)
    rw [key, pull_evc, pull_evc]
    exact e

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmLineBundleIsoDescendsSubringFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem symm_lbIso_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsym
  haveI := hB.proper
  have hprop : IsProper (G2 B).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : QuasiCompact (G2 B).hom := inferInstance
  haveI : QuasiSeparated (G2 B).hom := inferInstance
  set sw₀ := (lift (snd B B) (fst B B)).left with hsw₀
  have hpb := isPullback_square hφ.1 φ₂ sq
  have H : LBIso (P₀.pull φ₂) ((P₀.pull sw₀).pull φ₂) :=
    LBIso.trans (pull_isLB hP₀ _) hP (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _) hsym
        (lbIso_square hP hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S (G2 A).left (G2 B).left (G2 A).hom
    (G2 B).hom φ₂ P₀ (P₀.pull sw₀) hpb hP₀ (pull_isLB hP₀ _) H
  refine ⟨F, fun R₁ h hF₁ => ?_⟩
  have hpb₁ := isPullback_square (isGrpPullback (spMap (Subring.inclusion h)) B).1 _
    (isSquare (spMap (Subring.inclusion h)) B)
  have H₁ := hF R₁ h hF₁ _ _ _ hpb₁
  have e := lift_swap (spMap (Subring.inclusion h)) B
  refine LBIso.trans (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB (pull_isLB hP₀ _) _) H₁ ?_
  exact lbIso_square (pull_isLB hP₀ _) hP₀ (lbIso_refl (pull_isLB hP₀ sw₀)) e.symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisGenericPoint
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatModel.LiftGen

theorem one_left_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] (P : Over S) :
    (1 : P ⟶ G).left = P.hom ≫ eSec G := by
  rw [CategoryTheory.Hom.one_def]
  simp [eSec]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem epsMul_comp_alg {R : Type} [CommRing R] (c : R) :
    (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul]

theorem fst_comp_epsMul {R : Type} [CommRing R] (c : R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (epsMul c) = (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun z => ?_
  simp [epsMul]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun z => ?_
  simp [dualMap]

theorem exists_lift_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ cf : Fin g → L, ∃ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left,
      IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf (w ≫ Y.m.φ) ∧ IsTanAtG Y.oF.t yL w := by
  intro E _ _ _ H Dw l' Xo' c' W Y A _ ξ g e he L _ io yL hyL cf
  have hv : ∀ i, IsTanAtG Y.t (yL ≫ Y.j) (bcV Y.t io e i) := by
    intro i
    obtain ⟨h1, h2⟩ := he.1 i
    constructor
    · show (spMap (dualMap io) ≫ e i) ≫ Y.t.G.hom = _
      rw [Category.assoc, h1, ← Category.assoc, PullbackSections.spMap_comp_spMap, dualMap_comp_alg,
        ← PullbackSections.spMap_comp_spMap, Category.assoc, hyL]
    · show spMap _ ≫ spMap (dualMap io) ≫ e i = _
      rw [← Category.assoc, PullbackSections.spMap_comp_spMap, fst_comp_dualMap, ← PullbackSections.spMap_comp_spMap, Category.assoc, h2,
        one_left_eq, one_left_eq]
      simp only [Over.mk_hom]
      rw [hyL, Category.assoc]
  let u : Fin g → (tEpsG (yL ≫ Y.j) ⟶ Y.t.G) := fun i =>
    Over.homMk (spMap (epsMul (cf i)) ≫ bcV Y.t io e i) (by
      show (spMap (epsMul (cf i)) ≫ bcV Y.t io e i) ≫ Y.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL ≫ Y.j
      rw [Category.assoc, (hv i).1, ← Category.assoc, PullbackSections.spMap_comp_spMap, epsMul_comp_alg])
  let wG : Sp (DualNumber L) ⟶ Y.t.G.left := ((List.ofFn u).prod).left
  have hcomb : IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf wG := ⟨u, fun i => rfl, rfl⟩
  have hwG : wG ≫ Y.t.G.hom = (spMap (algebraMap L (DualNumber L)) ≫ yL) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    have := Over.w ((List.ofFn u).prod)
    simpa [wG, Model.j] using this
  let w : Sp (DualNumber L) ⟶ Y.oF.t.G.left := Y.m.cart.1.lift wG _ hwG
  have hwφ : w ≫ Y.m.φ = wG := Y.m.cart.1.lift_fst _ _ _
  have hwh : w ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL := Y.m.cart.1.lift_snd _ _ _
  refine ⟨w, hwφ ▸ hcomb, hwh, ?_⟩

  let δ : Over.mk (yL ≫ Y.j) ⟶ tEpsG (yL ≫ Y.j) := Over.homMk (spMap (TrivSqZeroExt.fstHom L L L).toRingHom) (by
    show spMap _ ≫ spMap (algebraMap L (DualNumber L)) ≫ yL ≫ Y.j = yL ≫ Y.j
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (algebraMap L (DualNumber L)) = RingHom.id L := by
      refine RingHom.ext fun z => ?_
      simp
    rw [this, spMap_id']
    exact Category.id_comp _)
  have hδu : ∀ i, δ ≫ u i = 1 := by
    intro i
    refine Over.OverMorphism.ext ?_
    show spMap _ ≫ spMap (epsMul (cf i)) ≫ bcV Y.t io e i = _
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, fst_comp_epsMul]
    exact (hv i).2
  have hδ : δ ≫ (List.ofFn u).prod = 1 := by
    have h := map_list_prod (Formalism.L2.Pj.preHom (G := Y.t.G) δ) (List.ofFn u)
    rw [List.map_ofFn] at h
    refine (congrArg _ rfl).trans (h.trans ?_)
    have hf : (⇑(Formalism.L2.Pj.preHom (G := Y.t.G) δ) ∘ u) = fun _ => 1 := by
      funext i
      exact hδu i
    rw [hf, List.ofFn_const, List.prod_replicate, one_pow]
  refine Y.m.cart.1.hom_ext ?_ ?_
  · show (spMap _ ≫ w) ≫ Y.m.cm.F = _
    rw [Category.assoc, hwφ]
    have h1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ wG = (δ ≫ (List.ofFn u).prod).left := rfl
    rw [h1, hδ, one_left_eq, one_left_eq, Category.assoc, Y.m.cm.e_comm, Y.m.base]
    rfl
  · rw [Category.assoc, hwh, Over.w (1 : Over.mk yL ⟶ Y.oF.t.G), ← Category.assoc, PullbackSections.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (algebraMap L (DualNumber L)) = RingHom.id L := by
      refine RingHom.ext fun z => ?_
      simp
    rw [this, spMap_id']
    exact Category.id_comp _

end GlobalTheory.FlatModel.LiftGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x' : KeyIn K) (φ : x'.P.A.left ⟶ x.P.A.left), KeyAtMap x' x f φ → ∀ (g : ℕ) (hg : x.P.g = g) (hg' : x'.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (pt' : I → (baseOver (Sp K) ⟶ x'.P.A)) (ϑ : I → R) (J : I → Fin g → R), (∀ i, (pt' i).left ≫ φ = spMap f ≫ (pt i).left) → ThJet x hg m pt ϑ J → ThJet x' hg' m pt' (fun i => f (ϑ i)) (fun i j => f (J i j)) := by
  first | exact @GlobalTheory.MBLow.thJet_of_keyAtMap | exact GlobalTheory.MBLow.thJet_of_keyAtMap | (intros; apply GlobalTheory.MBLow.thJet_of_keyAtMap <;> assumption)
end

