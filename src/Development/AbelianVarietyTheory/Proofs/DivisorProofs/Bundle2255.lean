import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0221

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpans
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.TateSpan

theorem exists_eq_p_smul_of_lev_one {p : ℕ} [Fact p.Prime] {M : Type} [CommGroup M]
    (s : GlobalTheory.HTLat.Tate p M) (hs : s.lev 1 = 1) :
    ∃ s' : GlobalTheory.HTLat.Tate p M, s = (p : ℤ_[p]) • s' := by
  have h1 : ∀ k, s.lev (k + 1) ^ p ^ k = 1 := fun k => by
    rw [add_comm, GlobalTheory.HTLat.Tate.lev_add_pow, hs]
  refine ⟨GlobalTheory.HTLat.Tate.mk (fun k => s.lev (k + 1)) fun k => ⟨h1 k, s.lev_succ (k + 1)⟩,
    GlobalTheory.HTLat.Tate.ext fun k => ?_⟩
  rw [GlobalTheory.HTLat.Tate.lev_smul, GlobalTheory.HTLat.Tate.lev_mk, GlobalTheory.PDiv.pow_digit_natCast (h1 k),
    s.lev_succ]

theorem span_range_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T),
    (∀ x : (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A), x ^ p = 1 → ∃ a, (tι a).lev 1 = x) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ := by
  intro E _ _ _ H Dw p _ _ P tι h
  set S := Submodule.span ℤ_[p] (Set.range tι)
  have hI : IsLocalRing.maximalIdeal ℤ_[p] ≤ (⊥ : Ideal ℤ_[p]).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hle : (⊤ : Submodule ℤ_[p] P.T) ≤ S ⊔ IsLocalRing.maximalIdeal ℤ_[p] • ⊤ := by
    intro t _
    have hx : t.lev 1 ^ p = 1 := by
      have := GlobalTheory.HTLat.Tate.lev_pow t 1
      rwa [pow_one] at this
    obtain ⟨a, ha⟩ := h _ hx
    have hs : (t - tι a).lev 1 = 1 := by
      have e := congrArg (·.lev 1) (show t = tι a + (t - tι a) by abel)
      simp only [GlobalTheory.HTLat.Tate.lev_add, ha] at e
      exact left_eq_mul.1 e
    obtain ⟨s', hs'⟩ := exists_eq_p_smul_of_lev_one _ hs
    have e : t = tι a + (p : ℤ_[p]) • s' := by rw [← hs']; abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨a, rfl⟩) (Submodule.smul_mem_smul ?_ trivial)
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hle)

end GlobalTheory.TateSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FJ

theorem dot_split {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u v : Fin g → ℂ) :
    u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

theorem quad_full {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (A : Matrix (Fin g') (Fin g') ℂ)
    (B : Matrix (Fin g') (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ) (v : Fin g → ℂ) :
    v ⬝ᵥ (Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v =
      zP σ v ⬝ᵥ A *ᵥ zP σ v + 2 * (zP σ v ⬝ᵥ B *ᵥ tP σ v) + tP σ v ⬝ᵥ D *ᵥ tP σ v := by
  rw [dot_split σ]
  have h1 : zP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = A *ᵥ zP σ v + B *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  have h2 : tP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = Bᵀ *ᵥ zP σ v + D *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  rw [h1, h2, dotProduct_add, dotProduct_add, mulVec_transpose, dotProduct_comm (tP σ v) (vecMul _ _),
    ← dotProduct_mulVec]
  ring

def thT {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) (n : Fin k → ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))

theorem thetaChar_eq_tsum {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) :
    thetaChar τ a b z = ∑' n, thT τ a b z n := rfl

theorem summable_thT {k : ℕ} {τ : Matrix (Fin k) (Fin k) ℂ} (hτ : (τ.map Complex.im).PosDef) {a : Fin k → ℂ}
    (ha : ∀ i, ((a i).re : ℂ) = a i) (b z : Fin k → ℂ) : Summable fun n => ‖thT τ a b z n‖ := by
  have hd : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin k) := hτ.add hτ.transpose
  refine (GlobalTheory.thetaSummable_holds (Fin k) (fun i => (a i).re) 0 (z + b) τ hd).congr fun n => ?_
  congr 1
  have hs : ReciprocityTheory.PTheta.shiftVec (fun i => (a i).re) n = (fun i => (n i : ℂ)) + a :=
    funext fun i => by simp [ReciprocityTheory.PTheta.shiftVec, ha i]
  have h0 : ReciprocityTheory.PTheta.ofRealVec (0 : Fin k → ℝ) = 0 := funext fun i => by simp [ReciprocityTheory.PTheta.ofRealVec]
  simp only [ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC, thT]
  rw [hs, h0, add_zero]
  congr 1
  ring

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem thT_full (S : Matrix (Fin r) (Fin r) ℂ) (Z : Fin g → ℂ) (n : Fin g → ℤ) :
    thT (d.full σ S) (d.aF σ) (d.bF σ) Z n =
      Complex.exp (Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (d.t22 + S) *ᵥ cv (tP σ n)) +
        2 * Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (tP σ Z + d.b2))) *
      thT d.τ d.a d.b (zP σ Z + d.t12 *ᵥ cv (tP σ n)) (zP σ n) := by
  have hz : zP σ ((fun i => (n i : ℂ)) + d.aF σ) = (fun i => ((zP σ n i : ℤ) : ℂ)) + d.a := by
    funext i; simp [zP, CD.aF]
  have ht : tP σ ((fun i => (n i : ℂ)) + d.aF σ) = cv (tP σ n) := by
    funext i; simp [tP, CD.aF, cv]
  have hz' : zP σ (Z + d.bF σ) = zP σ Z + d.b := by
    funext i; simp [zP, CD.bF]
  have ht' : tP σ (Z + d.bF σ) = tP σ Z + d.b2 := by
    funext i; simp [tP, CD.bF]
  unfold thT CD.full
  rw [quad_full, dot_split σ _ (Z + d.bF σ), hz, ht, hz', ht', ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

end GlobalTheory.MBLow.Cl.FJ

open GlobalTheory.MBLow.Cl.FJ in

theorem GlobalTheory.MBLow.Cl.fj_expansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm →
    ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧
      ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  intro N g' r g bX d σ S _ hpos Z
  let e : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) :=
    { toFun := fun n => (tP σ n, zP σ n)
      invFun := fun p j => Sum.elim p.2 p.1 (σ j)
      left_inv := fun n => by
        funext j
        rcases h : σ j with i | l
        · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
        · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
      right_inv := fun p => by ext <;> simp [zP, tP] }
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    simp only [CD.aF]
    rcases σ j with i | l
    · rcases d.ha i with h | h <;> simp [h]
    · simp
  let F : (Fin r → ℤ) × (Fin g' → ℤ) → ℂ := fun p => thT (d.full σ S) (d.aF σ) (d.bF σ) Z (e.symm p)
  have hF : Summable fun p => ‖F p‖ :=
    (e.symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) Z n‖)).mpr
      (summable_thT hpos haF (d.bF σ) Z)
  have hFc : Summable F := hF.of_norm
  have hkey : ∀ χ, d.fj σ S χ Z = ∑' m, F (bX.equivFun χ, m) := by
    intro χ
    have hcv : cv (bX.equivFun χ) = co bX χ := by
      funext l; simp [cv, co, Module.Basis.equivFun_apply]
    have hsymm : ∀ p, e (e.symm p) = p := e.apply_symm_apply
    simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left, F]
    congr 1
    funext m
    have h1 : tP σ (e.symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
    have h2 : zP σ (e.symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
    rw [thT_full, h1, h2, hcv]
  refine ⟨?_, ?_⟩
  · refine ((hF.prod).comp_injective bX.equivFun.injective).of_nonneg_of_le (fun _ => norm_nonneg _) fun χ => ?_
    rw [hkey χ]
    exact norm_tsum_le_tsum_norm (hF.prod_factor _)
  · have hre := bX.equivFun.toEquiv.tsum_eq (fun k => ∑' m, F (k, m))
    simp only [LinearEquiv.coe_toEquiv] at hre
    rw [tsum_congr hkey, hre, ← hFc.tsum_prod, thetaChar_eq_tsum, ← e.symm.tsum_eq]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlacesStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_half_moves_under_translate_other_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  first | exact @GlobalTheory.ThetaBaseMove.thAt_move | exact GlobalTheory.ThetaBaseMove.thAt_move | (intros; apply GlobalTheory.ThetaBaseMove.thAt_move <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaRightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem ug_eq_uj (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    UG (cA σ) (incM F J) = Formalism.UG.UJ (sigR (AF F) σ) (JR (AF F) Jᵀ) := by
  ext g
  show (g : Matrix _ _ _)ᵀ * incM F J * (g : Matrix _ _ _).map (cA σ) = incM F J ↔
    Formalism.UG.cT (sigR (AF F) σ) (g : Matrix _ _ _) * JR (AF F) Jᵀ * (g : Matrix _ _ _) = JR (AF F) Jᵀ
  have hc : (g : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = (g : Matrix _ _ _).map (sigR (AF F) σ) := by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  rw [hc, hJ, Formalism.UG.cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

def toHA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J ≃ₜ* HA (AF F) σ Jᵀ where
  toMulEquiv := MulEquiv.subgroupCongr (ug_eq_uj σ J)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem isMulRightInvariant_of_equiv {G H : Type} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (h : (μ.map e).IsMulRightInvariant) :
    μ.IsMulRightInvariant := by
  have he : Measurable e := e.continuous.measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  have hμ : μ = (μ.map e).map e.symm := by
    rw [Measure.map_map hs he]
    have : (e.symm : H → G) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  have h1 := h.map_mul_right_eq_self (e g)
  have hc : (fun x : G => x * g) ∘ (e.symm : H → G) = (e.symm : H → G) ∘ (fun y : H => y * e g) := by
    ext y; simp
  conv_lhs => rw [hμ]
  rw [Measure.map_map (measurable_mul_const g) hs, hc,
    ← Measure.map_map hs (measurable_mul_const _), h1, ← hμ]

theorem isMulRightInvariant (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF F) σ Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ Jᵀ))
  haveI : BorelSpace (HA (AF F) σ Jᵀ) := ⟨rfl⟩
  refine isMulRightInvariant_of_equiv (toHA σ J) μ ?_
  haveI : (μ.map (toHA σ J)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ (toHA σ J)
  obtain ⟨d, hd'⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  have hJ' : IsHermND σ Jᵀ := ⟨fun i j => hJ j i, by rw [Matrix.det_transpose]; exact hd.ne_zero⟩
  exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic F E _ _ _ _ _ σ hss (σ d - d) (sub_ne_zero.2 hd')
    (by rw [map_sub, hss]; abel) n Jᵀ hJ' (μ.map (toHA σ J)) this

theorem countable_subgroupOf_range {G H : Type} [Group G] [Group H] [Countable G] (f : G →* H)
    (K : Subgroup H) : Countable ((f.range).subgroupOf K) := by
  have hc : (Set.range f).Countable := Set.countable_range f
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun γ : (f.range).subgroupOf K =>
    (⟨γ.1.1, MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 γ.2)⟩ : Set.range f)) ?_
  intro a b hab
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b h => Units.ext h)
  unfold ratU
  exact countable_subgroupOf_range _ _

theorem thetaIntegral_translate : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp g _ h Φ hΦ y
  have hTB := GlobalTheory.T.theta_basic_properties hP F E σ B n d X W M χX χW om r s r' s' hp
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, theta om Φ (γ * x) (y * h) = theta om Φ x (y * h) := by
    intro γ hγ x
    have := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (y * h)
    rwa [one_mul] at this
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := isMulRightInvariant σ hp.base.cm X.J hp.herm.herm
    (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ
  haveI := countable_ratU σ X.J
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : M.I om (om (g, h) Φ) y = ∫ x in M.dom, theta om Φ (x * g) (y * h) ∂M.μ := by
    unfold Model.I theta
    congr 1
    funext x
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ g
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g) (fun x => theta om Φ x (y * h))
    ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd'.setIntegral_eq hp.good.dom (f := fun x => theta om Φ x (y * h)) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl

end GlobalTheory.ThetaRightTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BasisChange

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def cb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) : epsR R ⟶ G :=
  ∏ i, GrpTangent.epsScale (c i) ≫ v i

theorem comb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = cb c v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨fun i => GrpTangent.epsScale (c i) ≫ v i, fun i => rfl, by rw [List.prod_ofFn]; rfl⟩

theorem comp_prod' {T T' : Over (Sp R)} (s : T' ⟶ T) {J : Type} (S : Finset J) (u : J → (T ⟶ G)) :
    s ≫ ∏ i ∈ S, u i = ∏ i ∈ S, s ≫ u i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem cb_tan {n : ℕ} (c : Fin n → R) {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    IsTangent (cb c v) := by
  rw [GrpTangent.isTangent_iff, cb, comp_prod']
  exact Finset.prod_eq_one fun i _ => (GrpTangent.isTangent_iff _).1 (GrpTangent.isTangent_epsScale _ (hv i))

theorem scale_sum {w : epsR R ⟶ G} (hw : IsTangent w) {J : Type} (S : Finset J) (a : J → R) :
    GrpTangent.epsScale (∑ i ∈ S, a i) ≫ w = ∏ i ∈ S, GrpTangent.epsScale (a i) ≫ w := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GrpTangent.epsScale_zero_comp hw
  | insert j S hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, GrpTangent.epsScale_add_comp _ _ hw, ih]

theorem cb_cb {m n : ℕ} (a : Fin m → R) (M : Matrix (Fin m) (Fin n) R) {v : Fin n → (epsR R ⟶ G)}
    (hv : ∀ i, IsTangent (v i)) : cb a (fun i => cb (M i) v) = cb (Matrix.vecMul a M) v := by
  simp only [cb, comp_prod', GrpTangent.epsScale_mul_assoc]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← scale_sum (hv j)]
  rfl

theorem cb_single {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin n) :
    cb (Pi.single j 1) v = v j := by
  rw [cb, Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, GrpTangent.epsScale_one, Category.id_comp]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, GrpTangent.epsScale_zero_comp (hv i)]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem exists_unit {n : ℕ} {y y' : Fin n → (epsR R ⟶ G)} (hy : IsLieBasis y) (hy' : IsLieBasis y') :
    ∃ M : Matrix (Fin n) (Fin n) R, IsUnit M ∧ ∀ i, IsLieComb (M i) y (y' i) := by
  choose M hM using fun i => (hy.2 _ (hy'.1 i)).exists
  choose N hN using fun i => (hy'.2 _ (hy.1 i)).exists
  refine ⟨Matrix.of M, ?_, hM⟩
  have e : y' = fun i => cb (Matrix.of M i) y := funext fun i => (comb_iff _ _ _).1 (hM i)
  have h : Matrix.of N * Matrix.of M = 1 := by
    ext i j
    have k : y i = cb (Matrix.vecMul (N i) (Matrix.of M)) y := by
      rw [← cb_cb _ _ hy.1, ← e]
      exact (comb_iff _ _ _).1 (hN i)
    have := (hy.2 _ (hy.1 i)).unique ((comb_iff _ _ _).2 k) ((comb_iff _ _ _).2 (cb_single hy.1 i).symm)
    have := congrFun this j
    rw [Matrix.one_apply, Matrix.mul_apply]
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, eq_comm] using this
  exact IsUnit.of_mul_eq_one_right _ h

theorem basis_of_unit {n : ℕ} {v v' : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {M : Matrix (Fin n) (Fin n) R}
    (hM : IsUnit M) (h : ∀ i, IsLieComb (M i) v (v' i)) : IsLieBasis v' := by
  have e : v' = fun i => cb (M i) v := funext fun i => (comb_iff _ _ _).1 (h i)
  subst e
  refine ⟨fun i => cb_tan _ hv.1, fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hv.2 w hw
  obtain ⟨U, rfl⟩ := hM
  set M : Matrix (Fin n) (Fin n) R := U.val with hMU
  have hN : M * U.inv = 1 := U.val_inv
  have hN' : U.inv * M = 1 := U.inv_val
  have key : ∀ b, IsLieComb b (fun i => cb (M i) v) w ↔ Matrix.vecMul b M = c := fun b => by
    rw [comb_iff, cb_cb _ _ hv.1, ← comb_iff]
    exact ⟨fun q => hu _ q, fun q => by rw [q]; exact hc⟩
  refine ⟨Matrix.vecMul c U.inv, (key _).2 ?_, fun b hb => ?_⟩
  · rw [Matrix.vecMul_vecMul, hN', Matrix.vecMul_one]
  · rw [← (key b).1 hb, Matrix.vecMul_vecMul, hN, Matrix.vecMul_one]

end GlobalTheory.MBLow.BasisChange

theorem GlobalTheory.MBLow.key_basis_change : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  intro κ hκ R K _ _ _ f x G _ _ φ hφ y y' v' hy hy' hv hv'
  obtain ⟨M, hM, hMy⟩ := GlobalTheory.MBLow.BasisChange.exists_unit hy hy'
  have hc : ∀ i, IsLieComb ((M.map f) i) x.v (v' i) := fun i =>
    Chart.comb_baseChange f hφ (hMy i) hv (hv' i)
  let _ := x.P.isAb.comm
  have hb : IsLieBasis v' := GlobalTheory.MBLow.BasisChange.basis_of_unit x.basis (hM.map f.mapMatrix) hc
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  refine ⟨hb, hd.unit ^ 4, ?_⟩
  have := hκ K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne v' hb 1 (M.map f)
    (fun i => by rw [show Geo.Tor.constFn x.P.A.hom _ (1 : K) = 1 by simp [Geo.Tor.constFn], _root_.one_mul]) hc
  have e : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  rw [e] at this
  simpa using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem key_value_of_nf : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  intro κ hH hT g x hg u τ a b c Mx h
  subst hg
  obtain ⟨h₁, h₂, ha, hb, hc, hΛ, hr, hs, hd⟩ := h
  have hW := GlobalTheory.KeyFormulaCompare.det_ne_zero x u ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx) hd
  have hM : Mx.det ≠ 0 := by
    rw [Matrix.det_smul] at hW
    exact right_ne_zero_of_mul hW
  refine ⟨hM, ?_⟩
  have hN : KeyPow.NormalAt x τ Mx a b c := ⟨u, h₁, h₂, hΛ, hr, hs, hd⟩
  obtain ⟨P, hg, rig, hr', th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, h₀, e₁, e₂⟩ := KeyConst.exists_rescale _ _ _ _ _ _ _ _ _ _ _ _ _ hc hM hN
  obtain ⟨u₀, t₁, t₂, t₃, t₄, t₅, t₆⟩ := (KeyPow.normalAt_one_iff _ _ _ _).1 h₀
  have h₃ := hH ℂ P hg rig hr' th₀ hth₀ v₀ hv₀ th hth v hv c Mx e₁ e₂
  have h₄ := hT _ u₀ _ _ _ t₁ t₂ ha hb t₃ t₄ t₅ t₆
  rw [h₄, Units.val_one, _root_.mul_one] at h₃
  rw [mul_comm]
  exact h₃.trans (_root_.mul_one _)

end GlobalTheory.MBLow.Cl
end

