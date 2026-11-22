import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepHoldsPullback
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.GrCl.Annih

theorem exists_trans {X : Scheme.{0}} {F : X.Modules} {V₁ V₂ : X.Opens} {n₁ n₂ : ℕ} {m₁ : Fin n₁ → Γ(F, V₁)}
    {m₂ : Fin n₂ → Γ(F, V₂)} (h₁ : VB.IsFrame m₁) (h₂ : VB.IsFrame m₂) :
    ∃ (T : Matrix (Fin n₁) (Fin n₂) Γ(X, V₁ ⊓ V₂)) (T' : Matrix (Fin n₂) (Fin n₁) Γ(X, V₁ ⊓ V₂)),
      T * T' = 1 ∧ T' * T = 1 ∧ ∀ l, resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) (m₁ l) =
        ∑ i, T l i • resM F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (m₂ i) := by
  let b₁ := h₁.basis (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
  let b₂ := h₂.basis (inf_le_right : V₁ ⊓ V₂ ≤ V₂)
  refine ⟨(b₂.toMatrix b₁).transpose, (b₁.toMatrix b₂).transpose, ?_, ?_, fun l => ?_⟩
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · have := b₂.sum_toMatrix_smul_self b₁ l
    simp only [b₁, b₂, VB.IsFrame.basis_apply] at this
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem tanEv_trans {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {F : X.Modules} (θ : F ⟶ GlobalTheory.LieVB.omega t.G)
    {V₁ V₂ : X.Opens} {n : ℕ} {s : Γ(F, V₁)} {m : Fin n → Γ(F, V₂)} {c : Fin n → Γ(X, V₁ ⊓ V₂)}
    (e : resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) s = ∑ i, c i • resM F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (m i))
    (h₁ : ⊤ ≤ x ⁻¹ᵁ V₁) (h₂ : ⊤ ≤ x ⁻¹ᵁ V₂) (h : ⊤ ≤ x ⁻¹ᵁ (V₁ ⊓ V₂)) :
    tanEv t hv h₁ (θ.app V₁ s) = ∑ i, ev x _ h (c i) * tanEv t hv h₂ (θ.app V₂ (m i)) := by
  let L : Γ(GlobalTheory.LieVB.omega t.G, V₁ ⊓ V₂) →+ k := AddMonoidHom.mk' (tanEv t hv h) (tanEv_add t hv h)
  have e₁ : tanEv t hv h₁ (θ.app V₁ s) = L (θ.app _ (resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) s)) := by
    rw [app_resM]
    exact (tanEv_resM t hv h inf_le_left _).symm
  rw [e₁, e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, app_resM]
  refine (tanEv_smul t hv h _ _).trans ?_
  rw [tanEv_resM t hv h inf_le_right]
  rfl

theorem annih : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z₁.X) (α : D.C.A), ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α → ∃ (n' : ℕ) (a : Matrix (Fin n') (Fin (D.C.n α)) R) (a' : Matrix (Fin (D.C.n α)) (Fin n') R), a * a' = 1 ∧ a' * a = 1 ∧ ∀ (τ : (Y Z₁.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z₁.i).t (Y Z.i).t τ) (u : Vecs Dw (Y Z₁.i).t K), LocM.IsTrans Z.i Z₁.i τ mu → Z₁.FlagAt (spMap (algebraMap R K) ≫ z) u → ∀ (y : Sp K ⟶ Z.X), y = spMap (algebraMap R K) ≫ z ≫ g₀ → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ D.C.B α) (v : TanM (y ≫ Z.π) (Y Z.i).t.G) (i : Fin (Dw.mult t.σ)), (i : ℕ) < t.k → (tv v).left = u t.σ i ≫ mu.φ → ∀ j : Fin n', t.k ≤ (j : ℕ) → ∑ l, algebraMap R K (a j l) * D.crd α K y hy v l = 0 := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW t Z g D hg hL Z₁ g₀ hg₀ ⟨_, g₁, hg₁, hH⟩ R K _ _ _ _ z α hα
  obtain rfl : g₁ = g₀ ≫ g := MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW _ _ _ _ hg₁ (MapComp.isMap_comp hg₀ hg)
  obtain ⟨U, hU, V₁, n', m₁, a₁, hx, hUV, hm₁, hA⟩ := hH (z (IsLocalRing.closedPoint R))
  have hzU : ⊤ ≤ z ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) z hx).ge
  obtain ⟨V, m, hV, hm, hc⟩ := hL α
  obtain ⟨T, T', hT, hT', hTm⟩ := exists_trans hm₁ hm
  have hz₁ : ⊤ ≤ (z ≫ g₀ ≫ g) ⁻¹ᵁ V₁ := FlagMod.le_preimage_map _ hUV hzU
  have hz₂ : ⊤ ≤ (z ≫ g₀ ≫ g) ⁻¹ᵁ V := by
    rw [← Category.assoc]
    exact FlagMod.le_preimage_map _ hV hα
  have hz := FlagMod.le_preimage_inf hz₁ hz₂
  refine ⟨n', a₁.1.map (ev z U hzU) * T.map (ev _ _ hz), T'.map (ev _ _ hz) * (a₁⁻¹).1.map (ev z U hzU), ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T.map _), ← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((a₁⁻¹).1.map _), ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, hT',
      Matrix.map_one _ (map_zero _) (map_one _)]
  intro τ mu u hτ hu y ey hy v i hi hv j hj
  have hyo : Set.range y ⊆ Z.opn := by
    rintro _ ⟨q, rfl⟩
    rw [ey, ← Category.assoc, Scheme.Hom.comp_apply]
    exact CommonMod.map_mem_opn hg₀ (MapComp.range_subset_opn Z₁ hu ⟨q, rfl⟩)
  obtain ⟨τ₀, mu₀, -, hτ₀, e₀, -⟩ := hg.2 K y hyo
  have e₀' : (y ≫ Z.π) ≫ τ₀ = (y ≫ g) ≫ t.B.π := (Category.assoc _ _ _).trans e₀.symm
  obtain ⟨v', ev'⟩ := (pushE t.B.tMap (y ≫ g) rfl).surjective (pushE mu₀ _ e₀' v)
  have hv' : (tv v').left ≫ t.B.tMap.φ = (tv v).left ≫ mu₀.φ := congrArg (fun q => (tv q).left) ev'
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₀ mu
  have ew : spMap ((algebraMap R K).comp (ev z U hzU)) ≫ hU.fromSpec = spMap (algebraMap R K) ≫ z := by
    rw [← MapComp.sp_comp, Category.assoc, FlagMod.spMap_ev]
  have eyg : y ≫ g = spMap (algebraMap R K) ≫ z ≫ g₀ ≫ g := by simp only [ey, Category.assoc]
  have hyV : ⊤ ≤ (y ≫ g) ⁻¹ᵁ (V₁ ⊓ V) := eyg ▸ FlagMod.le_preimage_comp _ hz
  have hy₁ : ⊤ ≤ (y ≫ g) ⁻¹ᵁ V₁ := FlagMod.le_preimage_mono inf_le_left hyV
  have hy₂ : ⊤ ≤ (y ≫ g) ⁻¹ᵁ V := FlagMod.le_preimage_mono inf_le_right hyV
  have key := hA K ((algebraMap R K).comp (ev z U hzU)) (tv v').left
  rw [ew, Category.assoc, ← eyg] at key
  replace key := key (isTan_tv v') hy₁ ⟨τ ≫ τ₀, mu', u, i,
    MapComp.isTrans_comp hg.1.1 hg₀.1.1 hτ₀ hτ mu' hmu', hu, hi, by rw [hv', hv, hmu', Category.assoc]⟩ j hj
  have eev : ev (y ≫ g) _ hyV = (algebraMap R K).comp (ev _ _ hz) :=
    (FlagMod.ev_congr eyg _ _ (FlagMod.le_preimage_comp _ hz)).trans (FlagMod.ev_spMap _ _ _ _ _)
  rw [← key]
  simp only [hc τ₀ mu₀ hτ₀ K y hy hyo v _ (isTan_tv v') hy₂ hv', Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul,
    Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tanEv_trans t.B.t (isTan_tv v') t.L.N.incl (hTm l) hy₁ hy₂ hyV, eev, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

end GlobalTheory.GrCl.Annih
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linearIndependent_real_combination (g r d : ℕ) (x : Fin r → Fin g → ℂ)
    (e : Fin d → Fin r → ℝ) (hx : LinearIndependent ℝ x) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  rw [Fintype.linearIndependent_iff] at hx he ⊢
  intro c hc
  have hreal : ∀ i, (∑ m, (e i m : ℂ) • x m) = ∑ m, e i m • x m := by
    intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    funext k
    simp [Pi.smul_apply, Complex.real_smul]
  have h1 : ∑ m, (∑ i, c i * e i m) • x m = 0 := by
    have h0 : ∑ i, c i • ∑ m, e i m • x m = 0 := by
      simpa only [hreal] using hc
    rw [← h0]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 := hx _ h1
  refine he c ?_
  funext m
  simpa [Finset.sum_apply, Pi.smul_apply] using h2 m

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomain
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibreInt

theorem dens_neg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : dens (-B) y = dens B y := by
  unfold dens
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_neg, Matrix.neg_mul, lminor, lminor, submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg]
  simp

theorem shear_neg_J {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (-Jpq p q) Z = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
  simp [shear, Jpq, hQ, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_neg_add]

theorem flagConst_pos (m : ℕ) : 0 < flagConst m :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem lintegral_dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  intro r p q e he A hA v hv
  set Z := toMat v with hZ
  have hH : (hQ Z).PosDef := hv
  have hd := hH.det_pos
  have hu : IsUnit (hQ Z).det := hd.ne'.isUnit
  set B : Matrix (Fin p) (Fin p) ℂ := 1 + Z * (hQ Z)⁻¹ * Zᴴ with hB
  have hBp : B.PosDef := PosDef.one.add_posSemidef (hH.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hs : schur (shear (-Jpq p q) Z) = -B := by
    rw [shear_neg_J, schur, hB]
    simp
    abel
  have h22 : (shear (-Jpq p q) Z).toBlocks₂₂ = hQ Z := by rw [shear_neg_J, toBlocks_fromBlocks₂₂]
  have hdet : B.det = ((hQ Z).det)⁻¹ := by
    have e1 : (1 : Matrix (Fin q) (Fin q) ℂ) + (hQ Z)⁻¹ * Zᴴ * Z = (hQ Z)⁻¹ := by
      rw [Matrix.mul_assoc, ← nonsing_inv_mul _ hu, ← Matrix.mul_add, hQ, sub_add_cancel, Matrix.mul_one]
    rw [hB, Matrix.mul_assoc, det_one_add_mul_comm, e1, det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨d, hd0, hdd⟩ : ∃ d : ℝ, 0 < d ∧ (hQ Z).det = d := by
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hd
    exact ⟨_, h1, Complex.ext (by simp) (by simp [← h2])⟩
  have hpt : ∀ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) =
      (ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) b.1)) * ENNReal.ofReal (dens B b.2) := by
    intro b
    rw [GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular r p q e he A (v, b) (by rw [hA]; exact h22 ▸ hu), hA]
    simp only [← hZ]
    rw [h22, hs, dens_neg, hdd, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (dens_nonneg _ _)),
      mul_comm (dens (hQ Z) b.1)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, lintegral_prod_mul
    (f := fun y => ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) y))
    (g := fun y => ENNReal.ofReal (dens B y))
    ((measurable_dens _).ennreal_ofReal.const_mul _).aemeasurable (measurable_dens _).ennreal_ofReal.aemeasurable,
    lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hH, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hBp, hdet, hdd,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  have hp := flagConst_pos p
  have hq := flagConst_pos q
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [_root_.inv_zpow', ← mul_div_assoc _ _ (flagConst q), div_mul_div_comm, ← zpow_add₀ hd0.ne', ← zpow_add₀ hd0.ne', mul_comm (flagConst q)]
  congr 2
  push_cast
  ring

end GlobalTheory.FlagFibreInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitChartForm

theorem jK_apply_eq_bot (R : Type) [CommRing R] [IsDomain R] (p : Sp (FractionRing R)) :
    (jK R) p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal = ⊥
  rw [@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)

theorem ker_eq_spMap_bot {R S : Type} [CommRing R] [CommRing S] [IsDomain S] (φ : R →+* S) :
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) = spMap φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) :=
  PrimeSpectrum.ext rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem j_mem_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (w : Xo.XF c) :
    Y.j w ∈ abLocus Y.t.G := by
  have h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact h

end GlobalTheory.TraitChartForm

open GlobalTheory.TraitChartForm in

theorem GlobalTheory.TraitChartForm.main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (_ : SABMap tC Y.t (ξ ≫ genι Y)) (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X), IsMonomial PC.D.toPre (bdParam k m e) γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (ϖ : W), Irreducible ϖ → ∀ (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∀ (be : LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ϖ' : V), Irreducible ϖ' → ∀ (f : W →+* V) (ψ : ChartRing k m e →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y → ∀ (r : ℕ) (u : Vˣ), f ϖ = u * ϖ' ^ r → ∀ (n : Fin m → ℕ) (v : Fin m → Vˣ), (∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) → ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) := by
  intro E _ _ _ H D l Xo c Y k _ m e ξ tC mC PC γ hmonC W _ _ _ hW ϖ hϖ χ t mt P hr be hmon V _ _ _ hV ϖ' hϖ' f ψ hfi
    hfl hψl hc r u hu n v hv
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  have : CharZero (ChartRing k m e) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
  have hCI : IsIntegrallyClosed (ChartRing k m e) := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).2
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  have hCA : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) t
  obtain ⟨tCV, ⟨mCV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ) tC
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.comp rfl mt mV
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl mC mCV
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ) = spMap ψ ≫ ξ ≫ genι Y by rw [Category.id_comp, hc])
    n₁ n₂

  have j : Function.Injective ((algebraMap V (FractionRing V)).comp f) := (IsFractionRing.injective V _).comp hfi
  let g : FractionRing W →+* FractionRing V := IsFractionRing.lift j
  have eg : jK V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpV : PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm
  have hpCV : PolAt tCV (jK V) :=
    GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV
  obtain ⟨BC, -, genC, hgC, hwC, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tCV hpCV

  have hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Y.t.G := by
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    obtain ⟨w, hw⟩ := hr ⟨p, rfl⟩
    rw [← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]
    exact j_mem_abLocus Y w
  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)

  have hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  let Ww : Set (Sp W) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Ww :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww := by
    rw [ker_eq_spMap_bot, hfbot]
    refine ⟨(abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩
  have hψW : ∀ y, PsiUnitOn P.D.toPre y Ww := fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2
  obtain ⟨PV, e₁, he₁⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance
    hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩

  have hlocC : ∀ a ∈ maximalIdeal (ChartRing k m e), ψ a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)
  have hvne : ∀ i, ψ (bdParam k m e i) ≠ 0 := fun i h => by
    rw [hv i] at h
    exact mul_ne_zero (v i).ne_zero (pow_ne_zero _ hϖ'.ne_zero) h
  have hgenC : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum (ChartRing k m e)) ∈ abLocus tC.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne Y.t.semi mC.cart.1 _).1 ?_
    have key : (ξ ≫ genι Y) (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) =
        χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) :=
      (Scheme.Hom.comp_apply (spMap ψ) (ξ ≫ genι Y) _).symm.trans
        ((congrArg (fun g : Sp V ⟶ Y.X => g (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) hc).symm.trans
          ((Scheme.Hom.comp_apply (spMap f) χ _).trans (congrArg χ hfbot)))
    rw [key]
    exact hχgen
  let Wc : Set (Sp (ChartRing k m e)) := abLocus tC.G ∩ {p | ∏ i, bdParam k m e i ∉ p.asIdeal}
  have hWco : IsOpen Wc := (GlobalTheory.AbLocusOpen.isOpen_abLocus_local tC.G tC.semi).inter
    (PrimeSpectrum.isOpen_basicOpen (a := ∏ i, bdParam k m e i))
  have hkerC : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum (ChartRing k m e)) ∈ Wc := by
    refine ⟨hgenC, fun h => ?_⟩
    have h' : ψ (∏ i, bdParam k m e i) = 0 := (RingHom.mem_ker).1 h
    rw [map_prod] at h'
    exact Finset.prod_ne_zero_iff.2 (fun i _ => hvne i) h'
  have hψC : ∀ y, PsiUnitOn PC.D.toPre y Wc := fun y => hmonC.psiUnitOn y fun p hp => hp.2
  obtain ⟨PCV, e₂, he₂⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H (ChartRing k m e) V ψ tC tCV mCV PC Wc
    inferInstance hCI hCA inferInstance inferInstance hVc hlocC hWco Set.inter_subset_left hψC hkerC
    ⟨BC, genC, hgC, hwC⟩

  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tCV k₁ PV PCV inferInstance inferInstance hVc
  refine ⟨(e₁.trans e₃).trans e₂.symm, fun y => ?_⟩
  set y' := ((e₁.trans e₃).trans e₂.symm) y with hy'
  have hy2 : e₂ y' = e₃ (e₁ y) := by simp [hy']
  obtain ⟨u₀, nW, hnW, hcW⟩ := hmon y
  obtain ⟨u₁, h₁⟩ := he₁ y _ hcW
  obtain ⟨u₃, h₃⟩ := he₃ _ _ h₁
  obtain ⟨uC, nC, hnC, hcC⟩ := hmonC y'
  obtain ⟨u₂, h₂⟩ := he₂ y' _ hcC
  rw [hy2] at h₂
  obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂
  have hA : (w : V) * (u₃ * (u₁ * f (u₀ * ∏ i, ![ϖ] i ^ nW i))) =
      ((w * u₃ * u₁ * Units.map f.toMonoidHom u₀ * u ^ nW 0 : Vˣ) : V) * ϖ' ^ (r * nW 0) := by
    rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, hu]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    ring
  have hB : (u₂ : V) * ψ (uC * ∏ i, bdParam k m e i ^ nC i) =
      ((u₂ * Units.map ψ.toMonoidHom uC * ∏ i, v i ^ nC i : Vˣ) : V) * ϖ' ^ (∑ i, n i * nC i) := by
    rw [map_mul, map_prod]
    simp_rw [map_pow, hv, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    simp only [Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    ring
  have hexp : r * nW 0 = ∑ i, n i * nC i :=
    IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ' hϖ' _ _ _ _ (hA.symm.trans (hw.symm.trans hB))
  have h0 : be y y = 2 * nW 0 := by simpa using hnW 0
  calc (r : ℤ) * be y y = 2 * ((r * nW 0 : ℕ) : ℤ) := by rw [h0]; push_cast; ring
    _ = 2 * ((∑ i, n i * nC i : ℕ) : ℤ) := by rw [hexp]
    _ = ∑ i, (n i : ℤ) * γ i y' y' := by
      simp_rw [hnC]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Mult

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]

def cellMult {m : ℕ} (δ : Fin m → balForms bar X) : ℕ :=
  Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ (Set.range δ)))

def IsPrim (β : balForms bar X) : Prop :=
  ∀ (k : ℕ) (β' : balForms bar X), β = k • β' → k = 1

def maxMult (q : ℕ) (φ : InvFun O) : ℕ∞ :=
  ⨆ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X) (_ : Module.Projective O X)
    (_ : Module.finrank O X ≤ q) (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ)
    (_ : LinearIndependent ℤ δ) (_ : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)),
    ((cellMult bar fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) : ℕ∞)

variable {bar}

theorem not_isPrim_zero : ¬ IsPrim bar (0 : balForms bar X) := fun h => by
  have := h 0 0 (by simp)
  exact zero_ne_one this

end Mult

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolOrdPull

theorem idlAlong_pull {X Y : Scheme.{0}} (D : GlobalTheory.EffCartierData X) (π : Y ⟶ X) (h : D.KeepsRegular π)
    {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ Y) :
    idlAlong (D.pull π h).idealSheaf y = idlAlong D.idealSheaf (y ≫ π) := by
  obtain ⟨k, hk⟩ := D.exists_mem ((y ≫ π) (closedPoint A))
  have hk' : ⊤ ≤ (y ≫ π) ⁻¹ᵁ D.U k := (Scheme.preimage_eq_top_of_closedPoint_mem _ hk).ge
  have hk'' : ⊤ ≤ y ⁻¹ᵁ (D.pull π h).U k := hk'
  rw [GlobalTheory.TraitGen.idlAlong_idealSheaf_eq (D.pull π h) y k hk'', GlobalTheory.TraitGen.idlAlong_idealSheaf_eq D (y ≫ π) k hk']
  congr 2

end GlobalTheory.PolOrdPull

open GlobalTheory.PolOrdPull in
theorem GlobalTheory.TorRef.isPhiDiv_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (X : Model Xo c β) (Z : Model Xo c β') (π : Z.X ⟶ X.X) (ψ : InvFun (𝓞 E)) (DX : GlobalTheory.EffCartierData X.X) (h : DX.KeepsRegular π), Z.j ≫ π = X.j → Nonempty (SABMap Z.t X.t π) → IsPhiDiv ψ X DX → IsPhiDiv ψ Z (DX.pull π h) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' X Z π ψ DX h hj ⟨n⟩ hX
  intro W _ _ _ hW ϖ hϖ χ t m P hgen be hbe hmon
  obtain ⟨m₂, -⟩ := GlobalTheory.LevelCover.sab_comp m n rfl
  have hgen' : Set.range (jK W ≫ χ ≫ π) ⊆ Set.range X.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hgen ⟨w, rfl⟩
    refine ⟨z, ?_⟩
    rw [← hj, Scheme.Hom.comp_apply, hz]
    rfl
  obtain ⟨k, hk, hI⟩ := hX W hW ϖ hϖ (χ ≫ π) t m₂ P hgen' be hbe hmon
  exact ⟨k, hk, (idlAlong_pull DX π h χ).trans hI⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem matrix_mul_bounded_poly_growth : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g d R τ E ⟨C, k, hC⟩ hE j
  choose C' hC' using hE
  refine ⟨max C 0 * ∑ i, max (C' i) 0, k, fun s hs => ?_⟩
  have hp : (0:ℝ) ≤ (1 + ‖s‖) ^ k := pow_nonneg (by positivity) _
  have h1 : ∀ i, ‖τ s i j‖ ≤ max C 0 * (1 + ‖s‖) ^ k := fun i =>
    (norm_le_pi_norm (τ s i) j).trans ((norm_le_pi_norm (τ s) i).trans
      ((hC s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)))
  calc ‖∑ i, τ s i j • E s i‖ ≤ ∑ i, ‖τ s i j • E s i‖ := norm_sum_le _ _
    _ = ∑ i, ‖τ s i j‖ * ‖E s i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, (max C 0 * (1 + ‖s‖) ^ k) * max (C' i) 0 :=
        Finset.sum_le_sum fun i _ => mul_le_mul (h1 i) (le_max_of_le_left (hC' i s hs))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp)
    _ = max C 0 * (∑ i, max (C' i) 0) * (1 + ‖s‖) ^ k := by rw [← Finset.mul_sum]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartCompatibleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (a a' : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → SameFlag Z.ty (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) ((Z.fr a').bc φ') := by
  first | exact @GlobalTheory.FlagEmb.tie_glue | exact GlobalTheory.FlagEmb.tie_glue | (intros; apply GlobalTheory.FlagEmb.tie_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PresentationTangentCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : ℕ) (b : Bool) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin (M + 1) → Fin g → R), p.Prime → GlobalTheory.LineNorm.IsTanBasis t x e → Pres t x p b e h → ∀ (m : ℕ) (w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)), (∀ j, IsTanAtG t x (w j)) → (∀ (k : Type) [Field k] (ψ : R →+* k), (p : k) ≠ 0 → Pull.Ind t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ w j)) → ∀ i : Fin m, ∃ (a a' : ℕ) (A : Fin a → R) (B : Fin a' → R), (p : R) ∈ (Ideal.span (Set.range A)).radical ∧ (p : R) ∈ (Ideal.span (Set.range B)).radical ∧ ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)), GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ w j) i * ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ := by
  first | exact @GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio | exact GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio | (intros; apply GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedLevelEqParahoricWithTupleCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedLevel_eq_parahoric_with_tupleCharacter : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelPara (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ξ := by
  first | exact @GlobalTheory.MtPara.levelPara | exact GlobalTheory.MtPara.levelPara | (intros; apply GlobalTheory.MtPara.levelPara <;> assumption)
end

