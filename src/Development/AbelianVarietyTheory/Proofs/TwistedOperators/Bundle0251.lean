import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0229
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockJointHarmonicVectorsIffPolynomials
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAdaptedBasisUnitarySubstitution
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAtOneRealPlaceOverVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitary
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RatEll

theorem sig_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h, h, star_star]

theorem exists_cls_of_irreducible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Function.Bijective (diagH σ J F) ∧ ∀ γ : GRat σ J, Irreducible γ.1.1.charpoly → ∃ P : PPol σ n, γ.1.1.charpoly = P.1 ∧ ∃ q, HasCls P F J (diagH σ J F γ) q := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  refine ⟨GlobalTheory.T.unitaryRationalDiagonalHom_bijective F E σ n J, ?_⟩
  intro γ hirr
  have hm : Formalism.UG.cT (σ : E →+* E) γ.1.1 * J * γ.1.1 = J := γ.2
  have hs := GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal F E σ n J hJ.2 γ
  have hdet : γ.1.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp γ.1.isUnit).ne_zero
  have h0 : eval 0 γ.1.1.charpoly ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro hc
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]
  have hP : γ.1.1.charpoly.Monic ∧ Irreducible γ.1.1.charpoly ∧ γ.1.1.charpoly.natDegree = n ∧
      eval 0 γ.1.1.charpoly ≠ 0 ∧ γ.1.1.charpoly = sharp σ n γ.1.1.charpoly :=
    ⟨Matrix.charpoly_monic _, hirr, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], h0, hs⟩
  let P : PPol σ n := ⟨γ.1.1.charpoly, hP⟩
  refine ⟨P, rfl, ?_⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq F E σ n P γ.1.1 rfl
  obtain ⟨x, hx0, hxs, hxf⟩ := GlobalTheory.T.exists_unitaryTorus_traceForm_of_hermitian F E σ (sig_sig hσ) n P J hJ γ.1.1 hm φ hφ
  exact GlobalTheory.T.exists_normClass_of_rationalIsometry_traceForm F E σ n P J φ x hx0 hxs hxf γ hφ

end GlobalTheory.TrEll.RatEll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsZonalSphericalFunctionUnramifiedUnitary
section
open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists

open Formalism.UG

section Generic

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (K : Subgroup G) (g : G) : Set (G ⧸ K) := {x | ∃ a b : K, x.out = (a : G) * g * b}

theorem mem_cosetsIn_iff (x : G ⧸ K) (t : G) :
    x ∈ cosetsIn K t ↔ x.out ∈ DoubleCoset.doubleCoset t (K : Set G) K := by
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩

theorem cosetsIn_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    cosetsIn K g' = cosetsIn K g := by
  ext x
  rw [mem_cosetsIn_iff, mem_cosetsIn_iff, DoubleCoset.doubleCoset_eq_of_mem h]

theorem dosetInd_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    dosetInd ℂ K g' = dosetInd ℂ K g := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem h]

theorem cosetsIn_ncard_ne_zero (hK : IsCommensurated K) (g : G) : (cosetsIn K g).ncard ≠ 0 := by
  refine ((Set.ncard_pos (P.finite_cosets_in_doset hK g)).2 ⟨(g : G ⧸ K), ?_⟩).ne'
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem cosetsIn_one : cosetsIn K 1 = {((1 : G) : G ⧸ K)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, e⟩
    rw [← QuotientGroup.out_eq' x, e]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem (K.mul_mem a.2 b.2))
  · rintro rfl
    refine ⟨⟨((1 : G) : G ⧸ K).out, ?_⟩, 1, by simp⟩
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ K))
    simpa using K.inv_mem this

end Generic

theorem exists_isZonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  intro L _ _ _ ϖ σ q n hU α
  classical
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := GlobalTheory.LFun.SatCompare.satU_laws (n := n) hU α
  have hN : ∀ g : GU σ n, ((cosetsIn (KU σ n) g).ncard : ℂ) ≠ 0 := fun g =>
    Nat.cast_ne_zero.2 (cosetsIn_ncard_ne_zero hK g)
  let w : GU σ n → ℂ := fun g =>
    SatU ϖ q (dosetInd ℂ (KU σ n) g) (fun i => (α i : ℂ)) / ((cosetsIn (KU σ n) g).ncard : ℂ)
  have hw : ∀ g g' : GU σ n, g' ∈ DoubleCoset.doubleCoset g (KU σ n : Set (GU σ n)) (KU σ n) → w g' = w g :=
    fun g g' h => by simp only [w, dosetInd_eq h, cosetsIn_eq h]
  refine ⟨w, fun a b g => hw _ _ (DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, rfl⟩), ?_, fun h hh => ?_⟩
  · simp only [w, law.2.2, cosetsIn_one, Set.ncard_singleton, Nat.cast_one, div_one]
  refine GlobalTheory.LFun.hecke_induction (K := KU σ n)
    (p := fun f => hAct (KU σ n) f w 1 = SatU ϖ q f fun i => (α i : ℂ)) ?_ ?_ ?_ hh
  · simpa [hAct] using (law.2.1 0 0 (zero_mem _)).symm
  · intro f hf f' hf' e e'
    have fin : ∀ f ∈ Hecke ℂ (KU σ n), (Function.support fun x : GU σ n ⧸ KU σ n => f x.out • w (1 * x.out)).Finite :=
      fun f hf => (P.finite_support_cosets hK hf.2).subset fun x hx h0 => hx (by simp [h0])
    rw [law.1 _ hf _ hf', ← e, ← e', hAct, hAct, hAct]
    simp only [Pi.add_apply, add_smul]
    exact finsum_add_distrib (fin f hf) (fin f' hf')
  · intro r g
    have hfin := P.finite_cosets_in_doset hK g
    have hterm : ∀ x ∈ hfin.toFinset, (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = r * w g := fun x hx => by
      have hm := (mem_cosetsIn_iff x g).1 ((Set.Finite.mem_toFinset _).1 hx)
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_mem hm, one_mul, hw g _ hm]
      simp
    rw [law.2.1 r _ (Final.DosetIndMem _ _ ℂ g), hAct,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), Finset.sum_congr rfl hterm,
      Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]
    · have := hN g
      simp only [w]
      rw [← cosetsIn]
      field_simp
    · intro x hx
      rw [Set.Finite.coe_toFinset]
      by_contra h
      refine hx ?_
      show (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = 0
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_notMem (fun h' => h ((mem_cosetsIn_iff x g).2 h'))]
      simp

end GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivConjFrameToRealLieLoweringOperatorEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

open GlobalTheory.HolRead GlobalTheory.HolRead.AdExt GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem conj_frame_eq {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ} (hd : IsUnit G.det) (hx : IsUnit x.det)
    (h : xᴴ * G * x = S) (hS : S * S = 1) (A : Matrix (Fin n) (Fin n) ℂ) :
    G⁻¹ * (x * A * x⁻¹)ᴴ * G = x * (S * Aᴴ * S) * x⁻¹ := by
  have hxi : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hx
  have hix : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x hx
  have hxh : ∀ M : Matrix (Fin n) (Fin n) ℂ, xᴴ * (x⁻¹ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hix, conjTranspose_one, Matrix.one_mul]
  have hGi : G⁻¹ = x * S * xᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    calc x * S * xᴴ * G = x * S * (xᴴ * G * x) * x⁻¹ := by
          simp only [Matrix.mul_assoc, hxi, Matrix.mul_one]
      _ = 1 := by rw [h, Matrix.mul_assoc x S S, hS, Matrix.mul_one, hxi]
  have hG : G = x⁻¹ᴴ * S * x⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, hxi, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hxi, conjTranspose_one, Matrix.one_mul]
  rw [hGi, hG]
  simp only [conjTranspose_mul, Matrix.mul_assoc, hxh]

theorem sgn_mul_self (p a : ℕ) : (sgn p a : ℝ) * sgn p a = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem diag_single_diag {n : ℕ} (s : Fin n → ℝ) (c d : Fin n) :
    (diagonal fun a => ((s a : ℝ) : ℂ)) * (Matrix.single c d (1 : ℂ))ᴴ * (diagonal fun a => ((s a : ℝ) : ℂ)) =
      (s c * s d) • Matrix.single d c (1 : ℂ) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.single_apply,
    Matrix.smul_apply]
  by_cases hi : d = i <;> by_cases hj : c = j <;> subst_vars <;> simp [*]
  ring

variable {D : D7} {S T : HSp D}

theorem conjAt_single (C : Ctx S T) (R : RealPoints C.θ T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau)
    (c d : Fin T.rank) : conjAt T ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) =
      (-(sgn C.X.p0 c * sgn C.X.p0 d) : ℝ) • (B ρ * Matrix.single d c 1 * (B ρ)⁻¹) := by
  unfold Ctx.IsB sgnM at hB
  have hx : IsUnit (B ρ).det := isUnit_det_B C hB ρ
  have hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]
  have hsd := diag_single_diag (fun a : Fin T.rank => sgn C.X.p0 (a : ℕ)) c d
  simp only [conjAt]
  rw [conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hsd, Matrix.mul_smul, Matrix.smul_mul, neg_smul]

theorem conjL_I_smul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) :
    conjL (I • Z) = -(I • conjL Z) := by
  funext τ a b
  change conj (I * Z τ a b) = -(I * conj (Z τ a b))
  rw [map_mul, Complex.conj_I]
  ring

theorem conjL_unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) :
    conjL (unitFr τ c d) = unitFr τ c d := by
  funext τ' a b
  change conj (unitFr τ c d τ' a b) = unitFr τ c d τ' a b
  simp only [unitFr]
  split_ifs <;> simp

theorem toLie_I_conjL (C : Ctx S T) (R : RealPoints C.θ T) {B : C.Bas} (hB : C.IsB B) {Z : Frame C.X.Ψ T.rank}
    (hZ : Z ∈ unitLie C.X) : toLie R B (fun ρ => C.m.e ρ) (I • conjL Z) = 0 := by
  unfold Ctx.IsB sgnM at hB
  funext ρ
  apply Subtype.ext
  rw [toLie_I]
  have hx : IsUnit (B ρ).det := isUnit_det_B C hB ρ
  have hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]
  have key : (mat (conjL Z) (C.m.e ρ))ᴴ * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) +
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * mat (conjL Z) (C.m.e ρ) = 0 := by
    have hZe := hZ (C.m.e ρ)
    rw [mat_conjL]
    ext i j
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin T.rank) ℂ => (starRingEnd ℂ) (M i j)) hZe
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.map_apply, Matrix.zero_apply, ← starRingEnd_apply, map_add, map_mul, map_zero,
      Complex.conj_conj, Complex.conj_ofReal] at h1 ⊢
    linear_combination h1
  have hMS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * (mat (conjL Z) (C.m.e ρ))ᴴ *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = -mat (conjL Z) (C.m.e ρ) := by
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left key, Matrix.mul_neg, ← Matrix.mul_assoc, hS,
      Matrix.one_mul]
  simp only [conjAt]
  rw [conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hMS, Matrix.mul_neg, Matrix.neg_mul, neg_neg, sub_self, smul_zero]
  rfl

theorem fderiv_toLieC_eq_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (φ : GA D T → ℂ), LowKilled C.θ T B φ → ∀ (g : GA D T) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  intro D S T C R B hB φ hφ g ρ c d hcd Z Z' hZ hZ' hsum
  obtain ⟨-, hk⟩ := hφ
  by_cases hf : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  swap
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp

  have hZ1 : toLieC C R B Z = toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) := by
    have e : Z = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d - I • Z' := by rw [← hsum, add_sub_cancel_right]
    rw [e]
    simp only [toLieC, LinearMap.comp_apply, map_sub, conjL_unitFr, conjL_I_smul, map_neg,
      toLie_I_conjL C R hB hZ', neg_zero, sub_zero]
  have hZ2 : toLieC C R B Z' = toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) := by
    have e : Z' = I • Z - I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d := by
      rw [← hsum, smul_add, smul_smul, I_mul_I, neg_one_smul]
      abel
    rw [e]
    simp only [toLieC, LinearMap.comp_apply, map_sub, conjL_I_smul, conjL_unitFr, map_neg,
      toLie_I_conjL C R hB hZ, neg_zero, zero_sub, neg_neg]
  rw [hZ1, hZ2]

  have hs : ∀ a : ℕ, sgn C.X.p0 a = 1 ∨ sgn C.X.p0 a = -1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  have hε : (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) * (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) =
      (1 : ℝ) := by
    have h1 := sgn_mul_self C.X.p0 c
    have h2 := sgn_mul_self C.X.p0 d
    linear_combination (sgn C.X.p0 (d : ℕ) * sgn C.X.p0 (d : ℕ)) * h1 + h2
  have hI : (1 / (2 * I) : ℂ) = -(I / 2) := by
    rw [one_div, mul_inv, Complex.inv_I]
    ring

  have hA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1 := by
    rw [toLie_val]
    simp only [mat_unitFr, if_true]
    rw [conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c]
    rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module
  have hBm : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1 := by
    rw [toLie_I]
    simp only [mat_unitFr, if_true]
    rw [conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c, hI]
    rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module
  have memA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈
      lieU (gramAt D T ρ) := by
    rw [hA]
    exact (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
      toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2
  have memB : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈
      lieU (gramAt D T ρ) := by
    rw [hBm]
    exact (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
      toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2

  have hN1 : toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) =
      HSMul.hSMul (α := ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T)
        (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memA⟩) := by
    funext ρ'
    apply Subtype.ext
    change (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memA⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1
    by_cases hρ : ρ' = ρ
    · subst hρ
      simp only [atPlace, Pi.single_eq_same]
      rw [hA, smul_smul, hε, one_smul]
    · simp only [atPlace, Pi.single_eq_of_ne hρ]
      rw [toLie_val]
      simp [mat_unitFr, hρ, conjAt]
  have hN2 : toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) =
      HSMul.hSMul (α := ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T)
        (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memB⟩) := by
    funext ρ'
    apply Subtype.ext
    change (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memB⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1
    by_cases hρ : ρ' = ρ
    · subst hρ
      simp only [atPlace, Pi.single_eq_same]
      rw [hBm, smul_smul, hε, one_smul]
    · simp only [atPlace, Pi.single_eq_of_ne hρ]
      rw [toLie_I]
      simp [mat_unitFr, hρ, conjAt]
  have hk1 := congrFun (hk ρ d c hcd) g
  simp only [RderC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk1
  have e1 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0)
      (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        Rder C.θ T ρ ((1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹))) φ g := by
    rw [hN1]
    exact (map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z)
      (fderiv_atPlace R g hf ρ ⟨_, memA⟩))
  have e2 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0)
      (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        Rder C.θ T ρ ((1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹))) φ g := by
    rw [hN2]
    exact (map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z)
      (fderiv_atPlace R g hf ρ ⟨_, memB⟩))
  rw [e1, e2]
  simp only [Complex.real_smul]
  linear_combination (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) : ℂ)) * hk1

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTorusWeightsFiniteDimensionalSubspaceStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torusWeights_finiteDimensional_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), FiniteDimensional ℂ S → ∃ F : Finset (Fin n → ℝ), ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v → μ ∈ F := by
  first | exact @GlobalTheory.TorusWtFin.finite_weights | exact GlobalTheory.TorusWtFin.finite_weights | (intros; apply GlobalTheory.TorusWtFin.finite_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockJointHarmonicVectorsIffPolynomialsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJointHarmonic_vectors_iff_polynomials : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → Graded κ → ∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ) := by
  first | exact @GlobalTheory.ArchRec.JointTransfer.isJoint_iff_cJoint | exact GlobalTheory.ArchRec.JointTransfer.isJoint_iff_cJoint | (intros; apply GlobalTheory.ArchRec.JointTransfer.isJoint_iff_cJoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniqueneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔ Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧ (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ → ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧ ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ → CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  first | exact @GlobalTheory.ArchRec.Joint.joint_harmonics | exact GlobalTheory.ArchRec.Joint.joint_harmonics | (intros; apply GlobalTheory.ArchRec.Joint.joint_harmonics <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussiansStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_smooth_family_complexGaussians : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.FockFamily.fock_vacua_family | exact GlobalTheory.FockFamily.fock_vacua_family | (intros; apply GlobalTheory.FockFamily.fock_vacua_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAdaptedBasisUnitarySubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_adaptedBasis_unitary_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ BS BT, IsAdapted (gramAt D S τ) sS BS → IsAdapted (gramAt D T τ) sT BT → ∃ ς : LPol T.rank S.rank ≃ₗ[ℂ] LPol T.rank S.rank, Graded ς ∧ (∀ P Q, fockIp (ς P) (ς Q) = fockIp P Q) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ P, ptAt ψ θ S T τ sS sT BS BT f P = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f (ς P) := by
  first | exact @GlobalTheory.ArchRec.BasisChange.ptAt_basis | exact GlobalTheory.ArchRec.BasisChange.ptAt_basis | (intros; apply GlobalTheory.ArchRec.BasisChange.ptAt_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAtOneRealPlaceOverVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → (∀ P, IsThetaFunO ψ S T (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P)) ∧ (f ≠ 0 → Function.Injective (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ N, Fischer (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) (ipTh μ 𝓕) (LinearEquiv.refl ℂ _) N) := by
  first | exact @GlobalTheory.OnePlaceFock.fock_at_one_place | exact GlobalTheory.OnePlaceFock.fock_at_one_place | (intros; apply GlobalTheory.OnePlaceFock.fock_at_one_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_inner_eq_fockInnerProduct_mul_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ P Q, ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f P) (pureTensorO ψ θ S T sS sT BS BT f Q) = fockIp P Q * (nrm2 μ 𝓕 f : ℂ) := by
  first | exact @GlobalTheory.FockIsometry.ipO_pureTensorO | exact GlobalTheory.FockIsometry.ipO_pureTensorO | (intros; apply GlobalTheory.FockIsometry.ipO_pureTensorO <;> assumption)
end

