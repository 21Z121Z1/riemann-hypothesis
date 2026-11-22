import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOfMatRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.DiagMat

def act (M : Matrix (Fin 8) (Fin 8) ℤ) (X : Type) [AddCommGroup X] : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun c := fun v => ∑ u, M v u • c u
  map_zero' := by ext v; simp
  map_add' c d := by ext v; simp [smul_add, Finset.sum_add_distrib]

theorem act_apply (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) (v : Fin 8) :
    act M X c v = ∑ u, M v u • c u := rfl

theorem act_act (M N : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) :
    act M X (act N X c) = act (M * N) X c := by
  ext v
  simp only [act_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem act_one {X : Type} [AddCommGroup X] (c : Fin 8 → X) : act 1 X c = c := by
  ext v
  simp [act_apply, Matrix.one_apply]

theorem act_comp {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁] (M : Matrix (Fin 8) (Fin 8) ℤ)
    (π : X₀ →+ X₁) (c : Fin 8 → X₀) : act M X₁ (fun u => π (c u)) = fun u => π (act M X₀ c u) := by
  ext v
  simp [act_apply, map_sum, map_zsmul]

theorem matRel_iff (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) :
    MatRel W a b y y' ↔ act (W + W.transpose) X y' = Pi.single b (act (W + W.transpose) X y a) := by
  constructor
  · intro h; ext v; rw [act_apply, h v, Pi.single_apply]; rfl
  · intro h v; have := congrFun h v; rw [act_apply] at this; rw [this, Pi.single_apply]; rfl

end GlobalTheory.Poinc.Eq8.DiagMat

open GlobalTheory.Poinc.Eq8.DiagMat in

theorem GlobalTheory.Poinc.Eq8.exists_diag_of_matRel : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (Y X₀ X₁ : Type) [AddCommGroup Y] [AddCommGroup X₀] [AddCommGroup X₁] (m : Fin 8 → Fin 8 → (Y →+ Y)) (e₀ : Y ≃+ (Fin 8 → X₀)) (ρ : Y →+ (Fin 8 → X₁)), Function.Surjective ρ → (∀ a b y, MatRel W a b (e₀ y) (e₀ (m a b y))) → (∀ a b y, MatRel W a b (ρ y) (ρ (m a b y))) → ∃ π : X₀ →+ X₁, Function.Surjective π ∧ ∀ y u, ρ y u = π (e₀ y u) := by
  intro W hW Y X₀ X₁ _ _ _ m e₀ ρ hρ h₀ h₁
  set Q := W + W.transpose with hQ
  have hdet : IsUnit Q.det := by rw [hW.2]; exact isUnit_one
  have hQP : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have hPQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet

  let Ψ : (Fin 8 → X₀) →+ (Fin 8 → X₁) :=
    (act Q X₁).comp (ρ.comp ((e₀.symm : (Fin 8 → X₀) →+ Y).comp (act Q⁻¹ X₀)))
  have hΨ : ∀ z, Ψ (act Q X₀ (e₀ z)) = act Q X₁ (ρ z) := by
    intro z
    simp only [Ψ, AddMonoidHom.comp_apply, act_act, hPQ, act_one]
    simp
  have hE : ∀ a b c, Ψ (Pi.single b (c a)) = Pi.single b (Ψ c a) := by
    intro a b c
    set z := e₀.symm (act Q⁻¹ X₀ c) with hz
    have hc : act Q X₀ (e₀ z) = c := by simp [hz, act_act, hQP, act_one]
    have r0 := (matRel_iff W a b _ _).1 (h₀ a b z)
    have r1 := (matRel_iff W a b _ _).1 (h₁ a b z)
    rw [← hQ, hc] at r0
    rw [← hQ] at r1
    rw [← r0, hΨ, r1, ← hΨ, hc]
  let π : X₀ →+ X₁ := (Pi.evalAddMonoidHom (fun _ => X₁) 0).comp (Ψ.comp (AddMonoidHom.single (fun _ => X₀) 0))
  have hπ : ∀ b x, Ψ (Pi.single b x) = Pi.single b (π x) := by
    intro b x
    have := hE 0 b (Pi.single 0 x)
    simpa [π] using this
  have hdiag : ∀ c, Ψ c = fun u => π (c u) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    simp only [hπ]
    rw [← Finset.univ_sum_single (fun u => π (c u))]
  have key : ∀ y u, ρ y u = π (e₀ y u) := by
    intro y u
    have h1 : act Q X₁ (ρ y) = fun u => π (act Q X₀ (e₀ y) u) := by rw [← hΨ, hdiag]
    have h2 := congrArg (act Q⁻¹ X₁) h1
    rw [act_act, hPQ, act_one, act_comp, act_act, hPQ, act_one] at h2
    exact congrFun h2 u
  refine ⟨π, ?_, key⟩
  intro x
  obtain ⟨y, hy⟩ := hρ (fun _ => x)
  exact ⟨e₀ y 0, by rw [← key, hy]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveQDivisorOffPointAmpleClassStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_QDivisor_offPoint_ampleClass : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N₀ : LB X) (A : CartierDiv X) (x : X) (r : ℕ) (lam μ : ℚ), N₀.IsLB → IsNef ℂ N₀ → IsAmpleLB (toLB A) → 0 < r → lam ≤ 1 → 0 < μ → ∃ (M : ℕ) (E : CartierDiv X), 0 < M ∧ E.Eff ∧ x ∉ E.supp ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB E] : ℚ) / M = (1 - lam) * interNumRed ℂ C ![N₀] / r + μ * interNumRed ℂ C ![toLB A] := by
  first | exact @GlobalTheory.exists_eff_off_pt_ample_class | exact GlobalTheory.exists_eff_off_pt_ample_class | (intros; apply GlobalTheory.exists_eff_off_pt_ample_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenFrame_chartVectors_compactFlagSpace_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  first | exact @GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | exact GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | (intros; apply GlobalTheory.CompHS.exists_eigFrame_vecAt₀ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | exact GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighth_power_projections_extend_from_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G C : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj C] [IsCommMonObj C], IsSemiAbelian G → IsAbelianScheme C → ∀ pr' : Fin 8 → ((Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj C), (∀ a, IsMonHom (pr' a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ (Over.pullback (jK R)).obj C)), ∃! x : T' ⟶ (Over.pullback (jK R)).obj G, ∀ a, x ≫ pr' a = y a) → ∃ prO : Fin 8 → (G ⟶ C), (∀ a, IsMonHom (prO a)) ∧ (∀ a, (Over.pullback (jK R)).map (prO a) = pr' a) ∧ ∀ (T' : Over (Sp R)) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ G, ∀ a, x ≫ prO a = y a := by
  first | exact @GlobalTheory.PowExtend.exists_pow_projections | exact GlobalTheory.PowExtend.exists_pow_projections | (intros; apply GlobalTheory.PowExtend.exists_pow_projections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndomorphismOfLatticePreservingLinear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.UnifEndo

theorem exists_isMonHom_of_map_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : A ⟶ A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f := by
  intro A _ hA L g u F hF
  exact GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA
    (GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u) L u F hF

end GlobalTheory.UnifEndo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem eq_zero_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {l : ℕ} (hl : 2 ≤ l)
    (v : X) (h : ∀ n : ℕ, ∃ z : X, v = (l ^ n) • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N, N = (b.repr v i).natAbs := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ := h N
  have hd : ((l ^ N : ℕ) : ℤ) ∣ b.repr v i :=
    ⟨b.repr z i, by rw [hz, ← natCast_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul]⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_natCast, ← hN]
  exact Nat.lt_pow_self (by omega)

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

end GlobalTheory.Poinc.TorUniq

namespace GlobalTheory.Poinc.Eq8

open GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem torMatch_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ ρ', TorMatch U U' g β ρ → TorMatch U U' g β ρ' → ρ = ρ' := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ ρ' h h'
  have hL := GlobalTheory.firstFiveLaws
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => congrArg (algebraMap (FractionRing V) F) (hgK r)

  have img : ∀ {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S], GlobalTheory.Mum.Base S → ∀ {H : Over (Sp S)} [GrpObj H]
      [IsCommMonObj H], IsSemiAbelian H → ∀ {E : DegData S (maximalIdeal S)} {B : PolAV (Sp (FractionRing S))}
      (W : Unif (maximalIdeal S) E B H) [Algebra (FractionRing S) F] (k : ℕ), 1 ≤ k → ∀ p : QkPt E.toPre F k,
      ∃ x : TFK (R := S) F ⟶ B.A, QkToAkU W.toUnifPre F k p x := by
    intro S _ _ _ hS H _ _ hH E B W _ k hk p
    obtain ⟨x, hx⟩ := GlobalTheory.TorsionAnyChar.existsTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p
    exact ⟨x, (GlobalTheory.TorsionAnyChar.indAtTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p x).1
      (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩

  have key : ∀ k : ℕ, IsUnit (k : R) → ∀ τ' : Multiplicative D'.toPre.X →* Fˣ, τ' ^ k = 1 →
      ∀ χ, τ' (Multiplicative.ofAdd (ρ χ)) = τ' (Multiplicative.ofAdd (ρ' χ)) := by
    intro k hk τ' hτ' χ
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
    let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
    obtain ⟨q₁, y₁, t₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₁
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q₂, y₂, t₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₂
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q', y', t'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (F := F) (k := k) τ' hτ'
    obtain ⟨a₁, ha₁⟩ := img hR hG U k hk1 q₁
    obtain ⟨a₂, ha₂⟩ := img hR hG U k hk1 q₂
    obtain ⟨a', ha'⟩ := img hV hG' U' k hk1 q'
    have e₁ := h F hF k hk τ₁ τ' q₁ q' a₁ a' hτ' (fun _ => rfl) y₁ t₁ y' t' ha₁ ha'
    have e₂ := h' F hF k hk τ₂ τ' q₂ q' a₂ a' hτ' (fun _ => rfl) y₂ t₂ y' t' ha₂ ha'
    have e : a₁.left ≫ genMap U = a₂.left ≫ genMap U := e₁.trans e₂.symm

    have ea : a₁ = a₂ := by
      refine Over.OverMorphism.ext ?_
      have e' : a₁.left ≫ U.gen.inv.left = a₂.left ≫ U.gen.inv.left := by
        refine pullback.hom_ext ?_ ?_
        · simpa only [genMap, Category.assoc] using e
        · have w₁ := Over.w U.gen.inv
          have s : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := w₁
          rw [Category.assoc, Category.assoc, s, Over.w a₁, Over.w a₂]
      simpa using congrArg (· ≫ U.gen.hom.left) e'
    subst ea
    obtain ⟨z, hz, hh, hι, hadd⟩ := GlobalTheory.TorsionMapInj.qkToAk_injective_closed R (maximalIdeal R) hR.1 D A G hG U F k hk1
      q₁ q₂ a₁ ha₁ ha₂
    have hz0 : z = 0 := by
      rw [y₁, y₂, zero_add, eq_comm, ← natCast_zsmul] at hz
      exact (smul_eq_zero.1 hz).resolve_left (by exact_mod_cast hk0)
    subst hz0
    rw [GlobalTheory.TorusExt.isIota_iff_eq D.tau_bimult, map_zero] at hι
    subst hι
    rw [GlobalTheory.TorusExt.isAdd_iff_eq, add_zero] at hadd
    rw [hadd] at t₂
    have u := ((GlobalTheory.TorsionAnyChar.gtOnto_any hL R (maximalIdeal R) hR.1 D F).2.2.2.1 q₁.g t₁.1).unique t₁ t₂
    exact congrArg Units.val (DFunLike.congr_fun u (Multiplicative.ofAdd χ)) |> Units.ext
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  refine AddMonoidHom.ext fun χ => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_dvd hl2 _ fun n => ?_
  have hk : IsUnit ((l ^ n : ℕ) : R) := by simpa using hl.pow n
  have hkF : ((l ^ n : ℕ) : F) ≠ 0 := by
    have := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at this
    exact this.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : F) := ⟨hkF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (l ^ n)
  have hn0 : l ^ n ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨z, hz⟩ := exists_eq_add_nsmul (ζ := (hζ.isUnit hn0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ)
    (key (l ^ n) hk · · χ)
  exact ⟨-z, by rw [hz, smul_neg]; abel⟩

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeEmb.exists_equiv | exact GlobalTheory.CMTypeEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeEmb.exists_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.AbCoh

theorem isAffineOpen_preimage_of_isPullback (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
    (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : IsAffineOpen (φ ⁻¹ᵁ U.1) := by
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact U.2.preimage φ

theorem exists_equiv_globForm_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R R' _ _ _ X X' s s' φ h hF hC hF' hC' hfl hsu
  have hb : Function.Bijective (liftSemi (pullForm h.w)) :=
    GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family R' _ _ (liftSemi (pullForm h.w)) X.affineOpens (fun U ↦ Sec s' (φ ⁻¹ᵁ U.1))
      (fun U ↦ GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme R' X' s' hfl ⟨_, isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U⟩)
      (GlobalTheory.T.exists_affineOpen_map_maximal_proper R' X X' s' φ hsu)
      (fun U ↦ GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective R R' X X' s s' φ h hF hC hF' hC' U
        (isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U))
  refine ⟨LinearEquiv.ofBijective _ hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfBijectiveMapBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_away_of_bijective_kaehler_mapBaseChange : ∀ (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Algebra.Smooth A C] [Algebra.Smooth A B] (Q : Ideal B) [Q.IsPrime], Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) → ∃ f : B, f ∉ Q ∧ Algebra.Etale C (Localization.Away f) := by
  first | exact @GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange | exact GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange | (intros; apply GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point : ∀ (U Y : Scheme.{0}) (τ : U ⟶ Y), IsLocallyNoetherian Y → LocallyOfFiniteType τ → IsSeparated τ → ∀ x : U, (∃ O : U.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ Y) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Etale h ∧ PreconnectedSpace T ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ IsFinite (W.ι ≫ pullback.snd τ h) ∧ (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t := by
  first | exact @GlobalTheory.EtaleFinitePiece.main | exact GlobalTheory.EtaleFinitePiece.main | (intros; apply GlobalTheory.EtaleFinitePiece.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenMultipleHermitianPositiveCombinationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_multiple_hermitian_positive_combination : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  first | exact @GlobalTheory.Desc.HermComb.main | exact GlobalTheory.Desc.HermComb.main | (intros; apply GlobalTheory.Desc.HermComb.main <;> assumption)
end

