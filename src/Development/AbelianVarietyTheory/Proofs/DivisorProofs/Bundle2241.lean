import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixOfMassFrameDiagonal
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrthFrames

open Matrix
open scoped ComplexConjugate

theorem exists_perm_initial {r : ℕ} (P : Fin r → Prop) [DecidablePred P] :
    ∃ (σ : Equiv.Perm (Fin r)) (p : ℕ), ∀ a, P (σ a) ↔ (a : ℕ) < p := by
  classical
  let f : Fin r → ℕ := fun a => if P a then 0 else 1
  let σ := Tuple.sort f
  have hm : Monotone (f ∘ σ) := Tuple.monotone_sort f
  let S : Finset (Fin r) := Finset.univ.filter fun a => f (σ a) = 0
  refine ⟨σ, S.card, fun a => ?_⟩
  have hP : P (σ a) ↔ f (σ a) = 0 := by
    simp only [f]; split_ifs with h <;> simp [h]
  rw [hP]
  constructor
  · intro h0
    have hsub : Finset.Iic a ⊆ S := by
      intro b hb
      rw [Finset.mem_Iic] at hb
      have := hm hb
      simp only [Function.comp_apply] at this
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra h0
    have hsub : S ⊆ Finset.Iio a := by
      intro b hb
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Finset.mem_Iio]
      by_contra hba
      have := hm (not_lt.1 hba)
      simp only [Function.comp_apply] at this
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem exists_sgn_frame {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (hN : N.IsHermitian) (hd : N.det ≠ 0) :
    ∃ (X : Matrix (Fin r) (Fin r) ℂ) (p : ℕ),
      Xᴴ * N * X = diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  classical
  set U : Matrix (Fin r) (Fin r) ℂ := (hN.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) with hUdef
  set lam := hN.eigenvalues with hlam
  have hU : Uᴴ * N * U = diagonal fun k => ((lam k : ℝ) : ℂ) := by
    have h := hN.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [hUdef, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h ⊢
    rw [h]; rfl
  have hne : ∀ k, lam k ≠ 0 := by
    intro k hk
    apply hd
    rw [hN.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [← hlam, hk])
  obtain ⟨σ, p, hσ⟩ := exists_perm_initial fun k => 0 < lam k
  let s : Fin r → ℝ := fun a => (Real.sqrt |lam (σ a)|)⁻¹
  let Y : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun k a => if k = σ a then ((s a : ℝ) : ℂ) else 0
  refine ⟨U * Y, p, ?_⟩
  have e1 : (U * Y)ᴴ * N * (U * Y) = Yᴴ * (Uᴴ * N * U) * Y := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, hU]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply, Y, Matrix.of_apply, diagonal_apply]
  rw [Finset.sum_eq_single (σ a)]
  · by_cases hab : a = b
    · subst hab
      simp only [if_true, Complex.star_def, Complex.conj_ofReal]
      have hs : s a * lam (σ a) * s a = ReciprocityTheory.ChartRestriction.G.FD.sgn p a := by
        have habs : 0 < |lam (σ a)| := abs_pos.2 (hne _)
        have hsq : s a * s a = |lam (σ a)|⁻¹ := by
          simp only [s]
          rw [← mul_inv, Real.mul_self_sqrt habs.le]
        unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
        by_cases hpos : 0 < lam (σ a)
        · rw [if_pos ((hσ a).1 hpos)]
          calc s a * lam (σ a) * s a = (s a * s a) * lam (σ a) := by ring
            _ = 1 := by rw [hsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
        · have hneg : lam (σ a) < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hne _)
          rw [if_neg (fun h => hpos ((hσ a).2 h))]
          calc s a * lam (σ a) * s a = (s a * s a) * lam (σ a) := by ring
            _ = -1 := by
              rw [hsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hneg.ne]
      rw [← hs]; push_cast; ring
    · have : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [this, hab]
  · intro k _ hk
    simp [hk]
  · simp

theorem gram_eq_transpose {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.OrthFrames

namespace GlobalTheory.OrthFrames

open Matrix

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) :
    V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h0 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    have : V.hT.flip (V.frame.equivFun.symm v) = 0 := by
      refine V.frame.ext fun i => ?_
      have := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
      simp only [LinearMap.flip_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
        LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      exact mul_comm (v j) _
    exact congrArg (fun f => f x) this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

theorem gm_isHermitian (D : D7) (i : Fin D.R.m) (τ : D.host.E →+* ℂ) :
    (((GlobalTheory.MassLink.gm D i).map τ)ᵀ).IsHermitian := by
  haveI hcm : IsCMField D.host.E := D.host.isCMField_hostE
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MassLink.gm, Matrix.submatrix_apply, HSpace.gram]
  rw [← (Wc D i).herm.eq ((Wc D i).frame (Fin.cast (rank_Wc i).symm b))]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem gm_det_ne (D : D7) (i : Fin D.R.m) (τ : D.host.E →+* ℂ) :
    (((GlobalTheory.MassLink.gm D i).map τ)ᵀ).det ≠ 0 := by
  rw [Matrix.det_transpose]
  have e := RingHom.map_det τ (GlobalTheory.MassLink.gm D i)
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, map_ne_zero]
  simp only [GlobalTheory.MassLink.gm, Matrix.det_transpose]
  have e2 : (HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) =
      (HSpace.gram (Wc D i)).submatrix (finCongr (rank_Wc i).symm) (finCongr (rank_Wc i).symm) := rfl
  rw [e2, Matrix.det_submatrix_equiv_self]
  exact hspace_gram_det_ne _

theorem exists_orth_frames : ∀ (D : D7) (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∃ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (GlobalTheory.MassLink.psi D) D.R.r) (p0 : GlobalTheory.MassLink.psi D → ℕ),
      ∀ τ : GlobalTheory.MassLink.psi D, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := by
  intro D i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have key : ∀ τ : GlobalTheory.MassLink.psi D, ∃ (X : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (p : ℕ),
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) X =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    obtain ⟨X, p, hX⟩ := exists_sgn_frame _ (gm_isHermitian D i τ.1) (gm_det_ne D i τ.1)
    refine ⟨X, p, ?_⟩
    rw [gram_eq_transpose, hX, Matrix.diagonal_transpose]
  choose X p hX using key
  exact ⟨fun τ => X τ, p, fun τ => hX τ⟩

end GlobalTheory.OrthFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiAdditive
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.ConstDefCub

theorem isPullCubical_constPt : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq htan A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg1 hg2 hF
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation E H Dw l Xo c K y.x x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

end GlobalTheory.ConstDefCub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  first | exact @GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | exact GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | (intros; apply GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerateStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₁ → (h.geo f₁ f₂ th k).Birational := by
  first | exact @GlobalTheory.HSApp.birational_of_ratGen | exact GlobalTheory.HSApp.birational_of_ratGen | (intros; apply GlobalTheory.HSApp.birational_of_ratGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPointStatement
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_kernel_at_point : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint := by
  first | exact @GlobalTheory.HTKernel.hodgeTateKernelAtPoint | exact GlobalTheory.HTKernel.hodgeTateKernelAtPoint | (intros; apply GlobalTheory.HTKernel.hodgeTateKernelAtPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFunctionValuesClassicalUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.MBLow.Cl.HolB

variable {X Y : Scheme.{0}}

theorem valF_comp_app (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valF x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valF (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dif_pos h', dif_pos h]
    simp only [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dif_neg h', dif_neg h]

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := rfl

def psiB (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left)
    (hw : φ ≫ D.P.A.hom = x.P.A.hom ≫ spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) :
    x.P.A.left ⟶ (DegPre.BF D ℂ).left :=
  (lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
    (Over.homMk φ (by
      rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
      Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A)).left

theorem hol_ptB : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  intro R _ _ _ D N ν g d x u φ hφ hE U f
  have hw := hφ.1.w
  have key : ∀ z, ptB ν d z = (u.ex z).left ≫ psiB R D x φ hw := by
    intro z
    have h0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := Over.w (u.ex z)
    let e : TF (R := R) ℂ ⟶ Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) :=
      Over.homMk (u.ex z).left (by simp only [Over.mk_hom]; rw [← Category.assoc, h0]; exact Category.id_comp _)
    have he : e ≫ lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
        (Over.homMk φ (by
          rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
          Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A) = lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) := by
      rw [comp_lift]
      congr 1
      · ext; simp [e, h0]
      · ext; simp [e, hE z]
    rw [ptB, ← he]
    rfl
  have hs : {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (psiB R D x φ hw ⁻¹ᵁ U)} := by
    ext z
    simp only [Set.mem_setOf_eq, key z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := u.hol (psiB R D x φ hw ⁻¹ᵁ U) ((psiB R D x φ hw).app U |>.hom f)
  rw [hs]
  refine ⟨ho, hd.congr fun z _ => ?_⟩
  rw [← valF_eq_valAt', valF_comp_app, key z]

end GlobalTheory.MBLow.Cl.HolB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicUniformizationComplexBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.UnifTan

theorem valR_comp_eq {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  first
  | exact @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | (apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp ..)

theorem valF_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF p U f = valAt' p U f := by
  unfold valF valAt' valAt
  split_ifs <;> rfl

theorem valR_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR p U f = valAt' p U f := by
  unfold valR valAt' valAt
  split_ifs <;> rfl

theorem valAt'_comp_eq {X Y : Scheme.{0}} (p : Sp ℂ ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (p ≫ ψ) U f = valAt' p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  rw [← valR_eq_valAt', ← valR_eq_valAt', valR_comp_eq]

theorem prime_subsingleton : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
  constructor
  have key : ∀ (P : PrimeSpectrum (DualNumber ℂ)) (z : DualNumber ℂ), z ∈ P.asIdeal ↔ z.fst = 0 := by
    intro P z
    constructor
    · intro hz
      by_contra hne
      have hu : IsUnit z := (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (isUnit_iff_ne_zero.2 hne)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
    · intro hz
      have h2 : z * z = 0 := by
        ext <;> simp [hz]
      have : z * z ∈ P.asIdeal := by rw [h2]; exact P.asIdeal.zero_mem
      rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  intro P Q
  ext z
  rw [key P, key Q]

theorem top_le_of_red {X : Scheme.{0}} (p : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ (redE ℂ ≫ p) ⁻¹ᵁ U) :
    ⊤ ≤ p ⁻¹ᵁ U := by
  intro y _
  have hy : y = redE ℂ (IsLocalRing.closedPoint ℂ) := by
    haveI := prime_subsingleton
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [hy]
  exact this

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, Over.mk_hom, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    (u.ex 0).left = η[A].left := by
  have h1 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  rw [h1, Hom.one_def]
  simp

theorem isD_iff_isDiff : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (b' : epsR ℂ ⟶ x.P.A) (b : TE R ℂ ⟶ D.P.A), IsTangent b' → b'.left ≫ φ = b.left →
      ∀ W' : Fin g → ℂ, (IsD ν d W' b ↔ u.IsDiff W' b') := by
  intro R _ _ _ D N ν g d x u φ hφ hE b' b hb' hbb W'
  have hP : IsPullback x.P.A.hom φ (TF (R := R) ℂ).hom D.P.A.hom := by
    rw [tf_hom]; exact hφ.1.flip
  let e := hP.isoPullback
  let ψ : x.P.A.left ⟶ (DegPre.BF D ℂ).left := e.hom
  have hψi : ψ ≫ e.inv = 𝟙 _ := e.hom_inv_id
  have hpt : ∀ z, ptB ν d z = (u.ex z).left ≫ ψ := by
    intro z
    apply pullback.hom_ext
    · simp only [ptB, Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst]
      have := Over.w (u.ex z)
      simpa using this.symm
    · simp only [ptB, Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hE z
  have hb : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = b'.left ≫ ψ := by
    apply pullback.hom_ext
    · simp only [Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst, Over.homMk_left]
      have := Over.w b'
      simpa using this.symm
    · simp only [Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hbb.symm
  have hred : redE ℂ ≫ b'.left = (u.ex 0).left := by
    rw [ex_zero]; exact hb'
  have back : ∀ {A : Type} [CommRing A] (p : Sp A ⟶ x.P.A.left) (U' : x.P.A.left.Opens) (f' : Γ(x.P.A.left, U')),
      valR (p ≫ ψ) (e.inv ⁻¹ᵁ U') ((e.inv.app U').hom f') = valR p U' f' := by
    intro A _ p U' f'
    rw [← valR_comp_eq, Category.assoc, hψi, Category.comp_id]
  have valB : ∀ (U' : x.P.A.left.Opens) (h : ⊤ ≤ b'.left ⁻¹ᵁ U') (f' : Γ(x.P.A.left, U')),
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((b'.left.appLE U' ⊤ h).hom f') = valR b'.left U' f' := by
    intro U' h f'
    unfold valR
    rw [dif_pos h]
  constructor
  · intro hD U' h f'
    have h0 : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ (e.inv ⁻¹ᵁ U') := by
      have hc : (((u.ex 0).left ≫ ψ) ≫ e.inv) = redE ℂ ≫ b'.left := by
        rw [Category.assoc, hψi, Category.comp_id, hred]
      rw [hpt 0]
      show ⊤ ≤ (((u.ex 0).left ≫ ψ) ≫ e.inv) ⁻¹ᵁ U'
      rw [hc]
      exact fun y _ => h (Set.mem_univ ((redE ℂ) y))
    have k := hD _ ((e.inv.app U').hom f') h0
    simp only [hb, hpt, valF_eq_valAt', ← valR_eq_valAt', back] at k
    rw [valB U' h f', k]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, valR_eq_valAt']
  · intro hI U f h0
    have h1 : ⊤ ≤ b'.left ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
      apply top_le_of_red
      rw [hred]
      rw [hpt] at h0
      exact h0
    have hs := hI (ψ ⁻¹ᵁ U) h1 ((ψ.app U).hom f)
    rw [valB] at hs
    simp only [hb, hpt, valR_comp_eq, valF_eq_valAt', valAt'_comp_eq]
    ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      rw [← hred, ← valR_eq_valAt', (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ _ h1).2]
      rfl
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact hs

end GlobalTheory.UnifTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHoldsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_bound_holds : ∀ M : ℝ, HostN M := by
  first | exact @GlobalTheory.CovTop.Sizes.hostN | exact GlobalTheory.CovTop.Sizes.hostN | (intros; apply GlobalTheory.CovTop.Sizes.hostN <;> assumption)
end

