import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Sector
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.ClosedImmIdeal

theorem ideal_comap_preimage {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i]
    (J : W.IdealSheafData) (U : W.affineOpens) :
    (J.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ = Ideal.map (i.app U.1).hom (J.ideal U) := by
  rw [GlobalTheory.Principalise.comapIdealAffine J i U ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ le_rfl,
    Scheme.Hom.app_eq_appLE]

theorem iSup_preimage_affineOpens {T W : Scheme.{0}} (i : T ⟶ W) :
    ⨆ U : W.affineOpens, i ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem comap_map_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (a : T.IdealSheafData) :
    (a.map i).comap i = a := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : W.affineOpens => ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩) (iSup_preimage_affineOpens i) fun U => ?_
  rw [ideal_comap_preimage, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Ideal.map_comap_of_surjective _ (i.app_surjective U.1 U.2)]

theorem map_comap_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (b : W.IdealSheafData)
    (hb : (⊥ : T.IdealSheafData).map i ≤ b) : (b.comap i).map i = b := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap _ _)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : W.affineOpens => U)
    (iSup_affineOpens_eq_top W) fun U => ?_
  have h0 := hb U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h0 ⊢
  rw [ideal_comap_preimage, Ideal.comap_map_of_surjective _ (i.app_surjective U.1 U.2)]
  refine sup_le le_rfl (le_trans ?_ h0)
  simp

theorem map_sup_comap_and_comap_map : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
    ∀ (a : T.IdealSheafData) (J : W.IdealSheafData),
      (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  intro T W i hi a J
  haveI := hi
  refine ⟨?_, comap_map_eq i a⟩
  have hb : (⊥ : T.IdealSheafData).map i ≤ a.map i ⊔ J :=
    le_sup_of_le_left (Scheme.IdealSheafData.map_mono i bot_le)
  rw [← map_comap_eq i _ hb, Scheme.IdealSheafData.comap_sup, comap_map_eq]

end GlobalTheory.ClosedImmIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestMore
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.GenInterior

theorem exists_j₀_eq_genericPoint (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] :
    ∃ v : V₀ TF.Y Z, j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  obtain ⟨x, hx⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  have hxm : TF.Y.j x ∈ barComp TF.Y Z := (j_mem_barComp Z x).2 hx
  let v : V₀ TF.Y Z := ⟨x, hxm⟩
  have hU : IsOpen (Set.range (j₀ TF.Y Z)) := (j₀ TF.Y Z).isOpenEmbedding.isOpen_range
  exact ((genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff hU).2 ⟨j₀ TF.Y Z v, trivial, v, rfl⟩

end GlobalTheory.GenInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteFrameRealSpecialUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.TubePack

theorem det_eq_of_intertwine {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r)
    (U : Matrix ι ι ℂ) (A : Matrix ι (Fin r) ℂ) (B : Matrix (Fin r) ι ℂ) (M : Matrix (Fin r) (Fin r) ℂ)
    (hAB : A * B = 1) (h : U * A = A * M) : U.det = M.det := by
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have hM : M = B * U * A := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have h1 : B * U * A = (B.submatrix id e.symm * U.submatrix e.symm e.symm) * A.submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 : A.submatrix e.symm id * B.submatrix id e.symm = 1 := by
    have h0 := Matrix.submatrix_mul_equiv A B (⇑e.symm) (Equiv.refl (Fin r)) (⇑e.symm)
    rw [hAB, Matrix.submatrix_one_equiv] at h0
    exact h0
  have h3 : (A.submatrix e.symm id).det * (B.submatrix id e.symm).det = 1 := by
    rw [← Matrix.det_mul, h2, Matrix.det_one]
  rw [hM, h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  linear_combination (-U.det) * h3

theorem herm_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) : herm (-G) x y = -herm G x y := by
  simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem tube_disjoint : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x₀ : Frame Ψ V.rank) (σ : D.what₂.Tau ≃ Ψ) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank) (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (J : Type) (s : J → Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V) (F : J → Set (realSU Ψ Gm)) (ρ₀ : D.what₂.Tau), Gm = -(V.gram)ᵀ → IsInfFam θ → IsRealPart V θ A rp → IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) Ψ Gm x₀ σ A e → (∀ ρ, (σ ρ).1 = tauE D ρ) → (∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b) → (∀ j, ∀ γ ∈ inReal Ψ Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)), ∀ y ∈ F j, γ * y ∈ F j → γ = 1) → (∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧ ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j')) → (∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → finE V ((h j)⁻¹ * g * h j) ∈ K → γ ∈ ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)) → ∀ g ∈ GQ V, ∀ (j j' : J) (y : GA D V), (finE V ((h j)⁻¹ * y) ∈ K ∧ π (rp y) ∈ F j ∧ 0 < (UpqT.mat (rp y ρ₀)).det.im) → (finE V ((h j')⁻¹ * (g * y)) ∈ K ∧ π (rp (g * y)) ∈ F j' ∧ 0 < (UpqT.mat (rp (g * y) ρ₀)).det.im) → UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det = UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp (g * y) ρ₀)).det → g = 1 ∧ j = j' := by
  intro D V θ A rp Ψ Gm x₀ σ e π K Λ J s h F ρ₀ hGm hθ hrp hid hσ heq hF hlink1 hlink2 g hg j j' y hy hgy hsec
  obtain ⟨δ, hδU, hδeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  have hmat : matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) δ := hδeq.symm
  have h1 : (matHom V g).1 = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) := by rw [hmat]; rfl
  have hinf : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) g = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
    intro ρ
    have hinc : ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf D.host.F))).map (θ ρ) = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
      ext a b
      exact (hθ ρ).1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl
  have hK : finE V ((h j')⁻¹ * g * h j) ∈ K := by
    have := K.mul_mem hgy.1 (K.inv_mem hy.1)
    rw [← map_inv, ← map_mul] at this
    convert this using 2
    group
  obtain ⟨hint, hdj⟩ := hlink1 j j' g δ hg hmat hK
  have hconj : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = starRingEnd ℂ (τ x) := fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hU' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := hδU
  have hdd : (D.sp.cm.sig : D.host.E →+* D.host.E) (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := by
    have h2 := congrArg Matrix.det hU'
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    have hg0 := GlobalTheory.UnitaryGlue.gram_det_ne_zero V
    apply mul_right_cancel₀ hg0
    linear_combination h2
  have hnorm : ∀ φ : D.host.E →+* ℂ, ‖φ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det‖ = 1 := by
    intro φ
    have h2 := congrArg φ hdd
    rw [map_mul, hconj, map_one, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖φ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det‖ ^ 2 = 1 := by exact_mod_cast h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint hnorm
  have hpm := UpperTheory.Ram.Sector.pow_torsionOrder ⟨n, hn, hpow⟩
  have hdetρ : ∀ ρ, (UpqT.mat (rp g ρ)).det = tauE D ρ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
    intro ρ
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    refine det_eq_of_intertwine (e ρ) _ (A ρ) (mat x₀ (σ ρ) * (permM (e ρ))ᵀ) _ ?_ ?_
    · rw [← Matrix.mul_assoc, (hid ρ).2, permM_mul_transpose]
    · rw [hrp g ρ, hinf ρ]
  have hmul : (UpqT.mat (rp (g * y) ρ₀)).det = tauE D ρ₀ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det * (UpqT.mat (rp y ρ₀)).det := by
    rw [← hdetρ ρ₀, ← Matrix.det_mul, map_mul]
    rfl
  have hd1 : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := by
    have h4 := hgy.2.2
    rw [hmul] at h4 hsec
    have h5 := UpperTheory.Ram.Sector.eq_one_of_sec_eq (NumberField.Units.torsionOrder_pos D.host.E)
      (by rw [← map_pow, hpm, map_one]) hy.2.2 h4 hsec
    exact (tauE D ρ₀).injective (by rw [h5, map_one])
  have hjj := hdj hd1
  subst hjj
  have hstab := hlink2 j g δ hg hmat hd1 hK
  have hmemSU : embGL Ψ V.rank δ ∈ realSU Ψ Gm := by
    refine embGL_mem_realSU Ψ Gm δ hd1 fun x y' => ?_
    rw [hGm, herm_neg, herm_neg, hstab.2.1]
  have hin : (⟨embGL Ψ V.rank δ, hmemSU⟩ : realSU Ψ Gm) ∈ inReal Ψ Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hstab, rfl⟩)
  have heqv := heq ⟨embGL Ψ V.rank δ, hmemSU⟩ (rp g) (fun ρ => by
    rw [hrp g ρ, hinf ρ]
    show _ = A ρ * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ).1
    rw [hσ ρ]) (rp y)
  have hs1 := hF j _ hin (π (rp y)) hy.2.1 (by rw [← heqv, ← map_mul]; exact hgy.2.1)
  have hδ1 : δ = 1 := by
    have h5 := congrArg (fun s : realSU Ψ Gm => ((s.1 (σ ρ₀) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) hs1
    have h6 : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact h5
    exact Units.ext (Matrix.map_injective (σ ρ₀).1.injective h6)
  refine ⟨Subtype.ext ?_, rfl⟩
  rw [hδ1, map_one] at hmat
  exact hmat

end GlobalTheory.TubePack
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerFixesVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph

theorem vac_fixed' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hv k hk
  obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v k hk.1 _ hSB
  have h1 := GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB φ₁ hφ₁ hact hvac
  obtain ⟨c, rfl⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hw θ hθ hvac φ₁ hφ₁ h1
  have hc := GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place F E σ B a a' G X om om' hTr v w hw hv k hk c hact
  rwa [hc, one_smul] at hact

end GlobalTheory.InertSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertScalarLeft

theorem scalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT k hk c hc
  by_contra hne
  have hSB := (hTr.geo.hM'.vac v).1
  apply GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place F E σ B a a' G X om om' hTr v w hin hT
  have hmem : c • G.M'.vac v - G.M'.vac v ∈ augAt om' v :=
    Submodule.subset_span ⟨k, hk.1, _, hSB, _, Submodule.smul_mem _ c hSB, hc, rfl⟩
  have h1 : c - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : G.M'.vac v = (c - 1)⁻¹ • (c • G.M'.vac v - G.M'.vac v) := by
    rw [show c • G.M'.vac v - G.M'.vac v = (c - 1) • G.M'.vac v by rw [sub_smul, one_smul],
      smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ hmem

end GlobalTheory.InertScalarLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvr
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

noncomputable section

open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntEigTransport

theorem isTan_iff_isTangent' {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

theorem transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  intro E _ _ _ H l c T io φ hio G S t x n τ k ub htan heig hbas
  have hz : ∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) → z = φ (embK c τ a) := by
    intro a z hz
    apply IsFractionRing.injective T.V T.Fr
    rw [hz, ← hio]; rfl
  have hE : ∀ w : epsR T.V ⟶ G.G, IsEigV c io G τ w ↔
      ∀ a, (w ≫ G.act.act a).left = spMap (epsScaleR (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ a)) ≫ w.left := by
    intro w
    constructor
    · intro h a
      exact h a (φ (embK c τ a)) (by rw [← hio]; rfl)
    · intro h a z hz'
      rw [hz a z hz']
      exact h a
  have hC : ∀ (a : Fin k → T.V) (w : epsR T.V ⟶ G.G), IsComb ub a w ↔ IsLieComb a ub w := fun a w => Iff.rfl
  have hv : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsEigBasis G.act (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) ub := by
    refine ⟨fun i => ⟨(isTan_iff_isTangent' _).1 (htan i), (hE _).1 (heig i)⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => hC a w).1 (hbas w ((isTan_iff_isTangent' _).2 hw.1) ((hE w).2 hw.2))
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.FlatRow.exists_eigenBasis n hv
  exact ⟨u, hu, fun i => (hu' i).symm⟩

end GlobalTheory.IntEigTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelComponentIrreducibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_component_irreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ U : (Xo'.XF c').Opens,
    (∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∃ Xw : Y.X.Opens, (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
      (∀ z, Y.j z ∈ Xw ↔ z ∈ U) ∧ GeomIrr Y.s Xw := by
  first | exact @GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open | exact GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open | (intros; apply GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelDomainOverInclusion
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

namespace GlobalTheory.ModelIntFr

set_option maxHeartbeats 1000000 in

theorem exists_intFr_of_modelPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → (∀ a : c'.V W, a ≠ 0 → IsUnit (β a)) → ∀ (T₀ : CDVR) (α : A →+* T₀.V), Function.Injective α → ∀ yy₀ : Sp T₀.Fr ⟶ Xo'.XF c', yy₀ ≫ Y.j = spMap ((algebraMap T₀.V T₀.Fr).comp α) ≫ ξ → ∃ (T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr), (∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) ∧ Function.Injective i ∧ IsLocalHom i ∧ ∃ (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = spMap iF ≫ yy₀ ≫ r) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hr A _ _ ξ β hξ hβ T₀ α _hα yy₀ hyy
  obtain ⟨io', hio'⟩ : ∃ io' : c'.F →+* T₀.Fr, spMap io' = yy₀ ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage (yy₀ ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  let io : c.F →+* T₀.Fr := io'.comp (IntermediateField.inclusion hle).toRingHom
  let yt : Sp T₀.V ⟶ Y.X := spMap α ≫ ξ
  have hz : yy₀ ≫ Y.j = spMap (algebraMap T₀.V (FractionRing T₀.V)) ≫ yt := by
    rw [hyy]
    simp only [yt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T₀.V), Nonempty (SABMap G Y.t yt) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨m2⟩⟩ : ∃ t' : SAB H (Sp T₀.Fr), Nonempty (SABMap t' G (spMap (algebraMap T₀.V T₀.Fr))) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
      sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T₀.V T₀.Fr)) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ :=
    GlobalTheory.DepthSum.thetaCore_trait E H Dw l' Xo' c' _ _ Y T₀.V yt yy₀ hz G m t' m2
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m2
  have cancel : ∀ (p : Sp T₀.Fr ⟶ Y.X) (_ : p = yy₀ ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t yy₀) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m3⟩ := cancel _ hz.symm n
  obtain ⟨m1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m3
  letI := io.toAlgebra
  have hx : (yy₀ ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c T₀.Fr := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc r, hr, Category.assoc,
      ← Category.assoc yy₀, ← hio']
    simp only [sOf, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨y, hy⟩ := GlobalTheory.AnyLevelFrame.exists_intFr T₀ io _ hx G t' m1 m2 θ hθ w2 σ' ⟨g2, r2⟩ hcl hgen
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  have key : io'.comp (c'.V W).subtype = ((algebraMap T₀.V T₀.Fr).comp α).comp β := by
    have e := congrArg (· ≫ Y.s) hyy
    simp only [Category.assoc, hjs, hξ] at e
    rw [← Category.assoc, ← hio'] at e
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at e
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hunit : ∀ b : c'.F, b ≠ 0 → b ∈ c'.V W → vV T₀.V (io' b) = 0 := by
    intro b hb hbV
    have e := RingHom.congr_fun key ⟨b, hbV⟩
    simp only [RingHom.comp_apply] at e
    have hu : IsUnit (α (β ⟨b, hbV⟩)) := (hβ _ fun h => hb (congrArg Subtype.val h)).map α
    have ev : valV T₀.V (algebraMap T₀.V T₀.Fr (α (β ⟨b, hbV⟩))) = 1 := by
      rw [valV, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hu
    rw [show io' b = _ from e]
    simp [vV, ev]
  refine ⟨T₀, RingHom.id _, RingHom.id _, fun a => rfl, Function.injective_id, inferInstance, io, y, ?_, ?_⟩
  · intro a ha
    have hb : (IntermediateField.inclusion hle a : c'.F) ≠ 0 := by
      intro h; exact ha (by simpa using congrArg Subtype.val h)
    show vV T₀.V (io' (IntermediateField.inclusion hle a)) = 0
    rcases (c'.V W).mem_or_inv_mem (IntermediateField.inclusion hle a) with h | h
    · exact hunit _ hb h
    · have := hunit _ (inv_ne_zero hb) h
      rw [map_inv₀] at this
      unfold vV at this ⊢
      rw [map_inv₀, WithZero.log_inv] at this
      omega
  · show GlobalTheory.AllWt.ptF y.1 = spMap (RingHom.id T₀.Fr) ≫ yy₀ ≫ r
    rw [show spMap (RingHom.id T₀.Fr) = 𝟙 _ by simp [spMap], Category.id_comp]
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hr, ← Category.assoc, ← hio']
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.ModelIntFr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerFrame
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_dualFam_frame : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∃ (ta : Fin N → P.T) (w₁ : Fin (Dw.mult τ.1) → P.V) (w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V)
        (σ : Equiv.Perm (Ind Dw τ.1)),
        (∀ m, ((ta m).lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left) ∧
        (∀ k, w₁ k ∈ htLat c P τ.1 ∧ w₁ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₁ k ∈ P.eigV (embInt c P.integers τ.1)) ∧
        (∀ k, w₂ k ∈ htLat c P (conjEmb τ.1) ∧ w₂ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₂ k ∈ P.eigV (embInt c P.integers (conjEmb τ.1))) ∧
        ‖(Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 ∧
        ‖(Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 := by
  intro hK hTate hVal E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hOv hA N a T S hLat _ yb yy P π ψ y hHT β hβ
  obtain ⟨ta, u, hlev, hDF⟩ := hTate E H Dw l' Xo' c' W Y p n hs hA yb yy P π ψ hHT.1 β (conjEmb τ.1) (Ind Dw τ.1)
    N a T S hLat
  rw [htAt_embV_eq E H Dw l l' Xo Xo' c c' W Y r ν hle hOv p yb yy P π ψ y hHT β hβ (conjEmb τ.1)] at hDF
  obtain ⟨hPt, -, -, z, g, a0, x, -, -, -, hTie, hLB⟩ := hHT
  obtain ⟨-, -, hπ, hψpb, hgen, -⟩ := hPt
  have hact : ∀ b, (P.oA.act b).left ≫ ψ = ψ ≫ (Y.oF.t.act.act b).left := fun b =>
    Y.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Y.m.act, hgen, ← Category.assoc ψ, hgen, ← Category.assoc, P.gen_act,
        Category.assoc, hπ, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, hψpb.1.w, Over.w_assoc])
  have hact2 : ∀ b, (P.oA.act b).left ≫ (ψ ≫ ν.φ) = (ψ ≫ ν.φ) ≫ (Xo.univ.t.act.act b).left := fun b => by
    rw [← Category.assoc, hact, Category.assoc, ν.act, Category.assoc]
  have hpb2 := hψpb.comp ν.cart
  have heig : ∀ σ j, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) (x σ j) := fun σ j b =>
    ((hTie σ j).act b (hact2 b)).unique hpb2.1
      (by rw [z.eig σ j b, ← algebraMap_embInt P.integers]; exact (hTie σ j).scale _)
  have hK' := (hK p ℂ_[p] Valued.v 𝓞_ℂ_[p] (𝓞 E) P).2.2.2
  have hspan : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ Submodule.span ℂ_[p] (Set.range P.bLie) := fun σ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have heigV : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ P.eigV (embInt c P.integers σ) := fun σ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (heig σ j))
  have hmem : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ htLat c P σ := fun σ i =>
    ((hLB σ).2.le (Submodule.subset_span ⟨i, rfl⟩)).1
  have horth : ∀ k k', P.pairV (∑ j, g τ.1 k j • P.bLie (x τ.1 j))
      (∑ j, g (conjEmb τ.1) k' j • P.bLie (x (conjEmb τ.1) j)) = 0 := fun k k' => by
    have h1 : (∑ j, g τ.1 k j • P.bLie (x τ.1 j)) ∈ P.W := hK'.2.2.2.2.2.2 ▸ hspan _ _
    exact (hK'.2.2.2.2.1 _).1 h1 _ (hK'.2.2.2.2.2.2 ▸ hspan _ _)
  obtain ⟨lam, hlam, hsgn, σ, hσ⟩ := hVal E H Dw l c p hs P τ _ _ u hDF _ _ (fun k => heigV _ k) (fun k => heigV _ k)
    horth (hLB τ.1) (hLB (conjEmb τ.1))
  refine ⟨ta, _, _, σ, hlev, fun k => ⟨hmem _ k, hspan _ k, heigV _ k⟩, fun k => ⟨hmem _ k, hspan _ k, heigV _ k⟩,
    hσ, ?_⟩
  have e := congrArg norm (hsgn σ)
  have hs1 : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_mul, hlam, hσ, hs1, _root_.one_mul, _root_.one_mul] at e
  exact e.symm

end GlobalTheory.FlatModel
end

