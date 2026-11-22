import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialLatticeEndomorphismLiftStatement
section
open scoped TensorProduct NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_lattice_endomorphism_lift : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) → Module.Finite ℤ L →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    Module.Free ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) → Module.Finite ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    Module.finrank ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) = Fintype.card κ * Module.finrank ℚ E →
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M,
      ∀ (a : 𝓞 E) (r : κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E), f (((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) • r) = α a (f r) := by
  first | exact @GlobalTheory.TorusTateFree.tate_free_of_lattice | exact GlobalTheory.TorusTateFree.tate_free_of_lattice | (intros; apply GlobalTheory.TorusTateFree.tate_free_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreProduct_spec_fieldPoint_factors : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  first | exact @GlobalTheory.SpecFibreProduct.point_factors | exact GlobalTheory.SpecFibreProduct.point_factors | (intros; apply GlobalTheory.SpecFibreProduct.point_factors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldOfEtaleOnOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  first | exact @GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | exact GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | (intros; apply GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  first | exact @GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM | exact GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM | (intros; apply GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenFiniteCoproduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem finAff_sigma : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  intro κ _ B hB F
  classical
  have hfin : ∀ i, {y : B i | Sigma.ι B i y ∈ F}.Finite := fun i =>
    (F.finite_toSet).preimage (Sigma.ι B i).isOpenEmbedding.injective.injOn
  choose V hV hFV using fun i => hB i (hfin i).toFinset
  refine ⟨⨆ i, Sigma.ι B i ''ᵁ V i, IsAffineOpen.iSup_of_disjoint
    (fun i => (hV i).image_of_isOpenImmersion _) fun i j hij => ?_, fun x hx => ?_⟩
  · exact (disjoint_opensRange_sigmaι B i j hij).mono (Scheme.Hom.image_le_opensRange _ _)
      (Scheme.Hom.image_le_opensRange _ _)
  · obtain ⟨i, y, rfl⟩ := (sigmaOpenCover B).exists_eq x
    have hy : y ∈ V i := hFV i y ((Set.Finite.mem_toFinset _).2 hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hy, rfl⟩⟩

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

open CategoryTheory AlgebraicGeometry Limits NumberField in

theorem _root_.GlobalTheory.SiegelTor.finiteType_cycAway (n : ℕ) : Algebra.FiniteType ℤ (_root_.GlobalTheory.SiegelTor.cycAway n) := by
  have hfg : (Algebra.adjoin ℤ ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ)).FG := by
    rw [show ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ) = ↑({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Finset ℂ) by simp]
    exact Subalgebra.fg_adjoin_finset _
  have h := (Subalgebra.fg_iff_finiteType _).1 hfg
  rw [Algebra.adjoin_int] at h
  exact h

open CategoryTheory AlgebraicGeometry Limits NumberField in

theorem _root_.GlobalTheory.SiegelTor.arBase_cycAway : ∀ n : ℕ, n ≠ 0 → _root_.GlobalTheory.ZM.ArBase (_root_.GlobalTheory.SiegelTor.cycAway n).subtype := by
  intro n _
  exact ⟨_root_.GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n, _root_.GlobalTheory.SiegelTor.finiteType_cycAway n,
    Subtype.val_injective⟩

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRingStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cell_sep | exact GlobalTheory.FlagMod.FieldFlag.cell_sep | (intros; apply GlobalTheory.FlagMod.FieldFlag.cell_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodulesStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellFrames_lastStep_eigenmodules : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen | exact GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen | (intros; apply GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrameStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellPoint_image_and_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (b : A.B) (w : Pm Dw.mult) (S : Type) [CommRing S] (ψ₀ : Γ(Y.X, (A.V b).1) →+* S) (xc : CellVar Dw.mult → S) (z : Sp S ⟶ Z), z = spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w → z ≫ π = spMap ψ₀ ≫ (A.V b).2.fromSpec ∧ ∃ hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult), ∀ σ, (cellFrames hZ ht).uAt ((b, w) : A.B × Pm Dw.mult) z hz σ = (((A.k b).u σ).map ψ₀).submatrix id (w σ) * Matrix.of (cell xc σ) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cellpt | exact GlobalTheory.FlagMod.FieldFlag.cellpt | (intros; apply GlobalTheory.FlagMod.FieldFlag.cellpt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangularStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellFrameChangeTriangular_of_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), FlagCellFrameChangeTriangular hZ := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular | exact GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular | (intros; apply GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeries
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BaseCmp
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem unitOff_inv_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v)⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨inv_ne_zero (mul_ne_zero hu0 hv0), n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹⁻¹ = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by
      rw [inv_inv, pow_add]; ring
    rw [e]; exact hn1.mul hm1

theorem exists_unif' (E : Type) [Field E] [NumberField E] (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ ϖ : 𝓞 E, ϖ ≠ 0 ∧ ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 := by
  have hx : ∀ PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ∃ x ∈ PP.asIdeal, x ∉ PP.asIdeal ^ 2 := fun PP => by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ PP.asIdeal PP.ne_bot PP.isPrime.ne_top 1
  choose x hx1 hx2 using hx
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Q)
    (fun PP => PP.asIdeal) (fun _ => 2) (fun PP _ => Ideal.prime_of_isPrime PP.ne_bot PP.isPrime)
    (fun PP _ PP' _ h e => h (IsDedekindDomain.HeightOneSpectrum.ext e)) (fun PP => x PP.1)
  have key : ∀ PP ∈ Q, y ∈ PP.asIdeal ∧ y ∉ PP.asIdeal ^ 2 := fun PP hPP => by
    have h1 := hy PP hPP
    have hle : PP.asIdeal ^ 2 ≤ PP.asIdeal := Ideal.pow_le_self (by norm_num)
    refine ⟨?_, fun h => hx2 PP ?_⟩
    · have := PP.asIdeal.add_mem (hle h1) (hx1 PP)
      simpa using this
    · have := (PP.asIdeal ^ 2).sub_mem h h1
      simpa using this
  by_cases hQ : Q.Nonempty
  · obtain ⟨PP, hPP⟩ := hQ
    refine ⟨y, fun h0 => (key PP hPP).2 (h0 ▸ Ideal.zero_mem _), key⟩
  · refine ⟨1, one_ne_zero, fun PP hPP => absurd ⟨PP, hPP⟩ hQ⟩

theorem flatKer_holds : FlatKer := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV B hBg hB ξ ξR ω φ hK hQt N hN hNQ
  obtain ⟨eg, eQ, fg, heg, heQ, hfg, hflat⟩ := GlobalTheory.BaseCmp.flatTwoStep_holds D G Pl0 T0 A Ks R F hC i ξ B.de.chi ξR ω φ B hBg hB hK hK.chr
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif' D.host.E B.de.Q
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, hz, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i B.de.Q eQ heQ (ϖ : D.host.E) hϖE
  obtain ⟨κ, hκ, hact⟩ := GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hφ⟩ := GlobalTheory.T.tameKernel_vector_unit_mul_dilated_flat D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨Tm, hTm⟩ := hflat.1
  have hvT := hflat.2 Tm hTm
  have hφT := hφ Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    show Matrix.map (Matrix.map x fun w => incA D ((ϖ : D.host.E)⁻¹) * w) (fun w => incA D (ϖ : D.host.E) * w) = x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  have hvec : (princ B).vecBase = (κ * Gc)⁻¹ • ω (z, 1) φ := by
    rw [hφT, hact Tm hTm _ hSB]
    simp only [hcomp]
    have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i B.de.Q ξR eQ x) = Gc • flatDat R i B.de.Q ξR eQ := rfl
    rw [hsm, map_smul, ← hvT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]
  refine ⟨z, (κ * Gc)⁻¹, hz, unitOff_inv_mul' hκ hG, fun h P => ?_⟩
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  funext g
  rw [hvec, Pi.smul_apply, series_apply, series_apply, hB.fock_eq, hB.fock_eq, GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ z hz.2.1 1 (one_mem _) _ _ _ _ φ _ hth,
    map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePoints
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatCodimOne

theorem coheight_map_le_one {X Y : Scheme.{0}} (q : Y ⟶ X) (hq : GeneralizingMap q) (y : Y)
    (hy : Order.coheight y ≤ 1) : Order.coheight (q y) ≤ 1 := by
  have hy' := (Order.coheight_le_coe_iff (n := 1)).1 hy
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun z hz ↦ ?_
  obtain ⟨y', h₁, rfl⟩ := hq (show z ⤳ q y from hz.le)
  have hlt : y < y' := ⟨h₁, fun h ↦ hz.not_ge (Specializes.map h q.continuous)⟩
  have hm : IsMax y' := by simpa using hy' y' hlt
  have : IsMax (q y') := fun w hw ↦ by
    obtain ⟨y'', h₂, rfl⟩ := hq (show w ⤳ q y' from hw)
    exact Specializes.map (hm (show y' ≤ y'' from h₂)) q.continuous
  simpa using this

theorem preimage_contains_codim_le_one : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  intro X Y q _ W hW y hy
  show q y ∈ W
  apply hW
  rw [ringKrullDim_stalk_eq_coheight] at hy ⊢
  have h1 : Order.coheight y ≤ 1 := by exact_mod_cast hy
  have := coheight_map_le_one q (Flat.generalizingMap q) y h1
  exact_mod_cast this

end GlobalTheory.FlatCodimOne
end

