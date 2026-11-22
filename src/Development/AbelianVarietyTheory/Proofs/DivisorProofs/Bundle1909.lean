import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelComponentShortBasisBound
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.HSShort

theorem hsClaimS_component_geo : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k Λ₀ hH
  have hp := CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hb : (h.data f₁ f₂ th k).Birational := hH.bir
  have hd := ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ (h.data f₁ f₂ th k).geom hb hp.2
  have hh := GlobalTheory.T.height_birationalImage_eq_tuple_height hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ hH.totallyComplex (h.data f₁ f₂ th k).geom hb hp.2
  have hc := GlobalTheory.T.arithmeticHilbertSamuelBound hQ c.F (h.data f₁ f₂ th k) Λ₀ hH _ hh
  have hm := GlobalTheory.T.degree_supLattice_component_eq E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k P.T le_rfl
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  obtain ⟨-, eT, -, en, eL, eb, eD, eT', -⟩ := h.data_numbers f₁ f₂ th k
  rw [← hd, h.d_eq f₁ f₂ th k, eT, en, eL, eb, eD, eT', hm, hD, Int.cast_natCast] at hc
  exact hc

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecomposition
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertTwoFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g h : UA σ W.J}
    (hg : g ∈ GlobalTheory.InertSph.KAt σ W v) (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : g * h ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e : mat (g * h) = mat g * mat h := rfl
  have e' : mat (g * h)⁻¹ = mat h⁻¹ * mat g⁻¹ := by rw [mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h1 : u • (mat g - 1) = 0 := hg.1 u hu
    have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [e]; noncomm_ring
    rw [this, smul_add, ← Matrix.smul_mul, h1, h2, Matrix.zero_mul, add_zero]
  · rw [e, e', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {h : UA σ W.J}
    (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : h⁻¹ ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e1 : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by rw [Matrix.mul_sub, e1]; noncomm_ring
    rw [this, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hh.2 z hz).2, (hh.2 z hz).1⟩

theorem twoFac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  obtain ⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩ :=
    GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer F E σ B a a' G X om om' hT v w hin k hk
  obtain ⟨h, hh, hhY⟩ := GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ (a + a') G.W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  have eH : mat h = (1 - Y) * Np := by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]
  have eH' : (1 + Y) * mat h = 1 - Y := by
    rw [eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1,
      Matrix.mul_one]
  have eI : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  have intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]; exact add_mem hz (hYint z hz)
  refine ⟨k * h, mul_mem_KAt hk hh, h⁻¹, inv_mem_KAt hh, ?_, ?_, by group⟩
  · have e : mat (k * h) = mat k * mat h := rfl
    have h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1 := by
      have : (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]
      rw [e, ← Matrix.mul_assoc, this, hND1]
    refine ⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [← Matrix.mulVec_mulVec]; exact intY1 _ (hNDi z hz)
  · have h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1 := by
      rw [Matrix.mul_smul]
      have : (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
        have c : (1 + Y) * mat h = mat h * (1 + Y) := eH'.trans hhY.symm
        rw [Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]
        abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    refine ⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E (a + a') G.W v h2 _ (intY1 _ (hh.2 z hz).1)

end GlobalTheory.InertTwoFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplectic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLatSelfDual

theorem latAtV_selfDual_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _w _hin z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.InertLatSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinatesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (AE F E))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  first | exact @GlobalTheory.InertLocFrame.frame | exact GlobalTheory.InertLocFrame.frame | (intros; apply GlobalTheory.InertLocFrame.frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotentStatement
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
  (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  first | exact @GlobalTheory.InertPlace.inertQ_iff_nonSplitAt | exact GlobalTheory.InertPlace.inertQ_iff_nonSplitAt | (intros; apply GlobalTheory.InertPlace.inertQ_iff_nonSplitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameSpanCompletedEigenLatticeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_span_completed_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  first | exact @GlobalTheory.PtDeg.intFrame_span_eigLat | exact GlobalTheory.PtDeg.intFrame_span_eigLat | (intros; apply GlobalTheory.PtDeg.intFrame_span_eigLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqVolMulClassSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_vol_mul_classSum : ∀ {D : D7} (A : HSp D), A.gram = 1 → ∀ (m : Measure (Formalism.L2.Theta.GA D A)) (fd : Set (Formalism.L2.Theta.GA D A)),
    m.IsHaarMeasure → IsFundamentalDomain (GQ A) fd m →
    ∃ v : ℂ, v ≠ 0 ∧ ∀ (n : ℕ), n = A.rank → ∀ (pt : Formalism.MainNotions.StandardLatticesGL3.GA D n → Formalism.L2.Theta.GA D A),
      (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ Φ : Formalism.L2.Theta.GA D A → ℂ,
      (∀ γ ∈ GQ A, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ GinfC A, ∀ h, Φ (h * k) = Φ h) →
      (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D n) (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ h, Φ (h * k) = Φ h) →
      ∫ g in fd, Φ g ∂m = v * ∑ᶠ x : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n),
        ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out : ℂ))⁻¹ * Φ (pt x.out) := by
  first | exact @GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum | exact GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum | (intros; apply GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDual
section
noncomputable section

open NumberField
open scoped Pointwise

namespace GlobalTheory.VacRead.SelfDual

open GlobalTheory.InertSign (IntE hE)

theorem intE_iff {D : Formalism.BasicNotions.D7} {e : D.host.E} : IntE D e ↔ e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

theorem intE_gen (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {α₁ α₂ γ₁ γ₂ : D.host.E} (hα₁ : α₁ ∈ cE D cc) (hα₂ : α₂ ∈ cE D cc)
    (hγ₁ : γ₁ ∈ cE D D.host.ccK) (hγ₂ : γ₂ ∈ cE D D.host.ccK) :
    IntE D (r * D.host.conj α₁ * γ₁ / (Ideal.absNorm cc : D.host.E) *
      D.host.conj (r * D.host.conj α₂ * γ₂ / (Ideal.absNorm cc : D.host.E))) := by
  obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α₁ hα₁ α₂ hα₂
  obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ₂ hγ₂ γ₁ hγ₁
  unfold GlobalTheory.NormExact.IsScale at hs
  refine ⟨o₁ * o₂, ?_⟩
  simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj]
  change (o₁ : D.host.E) * (o₂ : D.host.E) = _
  field_simp
  linear_combination (exp := 1) (-(r * D.host.conj r) * (D.host.conj γ₂ * γ₁)) * h₁ +
    (-(r * D.host.conj r) * (Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E)) * h₂ +
    (-((Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E) * (o₂ : D.host.E))) * hs

def pairSpan (D : Formalism.BasicNotions.D7) (J : Submodule (𝓞 D.host.E) D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ u ∈ J, ∃ x ∈ J, t = u * D.host.conj x}

theorem conj_smul (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (c • x) = D.host.conj (c : D.host.E) * D.host.conj x := by
  rw [Algebra.smul_def, map_mul]

theorem intE_coe (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) : IntE D (c : D.host.E) := ⟨c, rfl⟩

theorem intE_mul_conj (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {u x : D.host.E} (hu : u ∈ bInv D cc r) (hx : x ∈ bInv D cc r) :
    IntE D (u * D.host.conj x) := by
  unfold bInv at hu hx
  induction hu using Submodule.span_induction generalizing x with
  | mem g hg =>
    obtain ⟨α₁, hα₁, γ₁, hγ₁, rfl⟩ := hg
    induction hx using Submodule.span_induction with
    | mem g' hg' =>
      obtain ⟨α₂, hα₂, γ₂, hγ₂, rfl⟩ := hg'
      exact intE_gen D cc r hn hs hα₁ hα₂ hγ₁ hγ₂
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [conj_smul, mul_left_comm]
      exact mul_mem (GlobalTheory.InertSign.IntE.conj (intE_coe D c)) hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem (hy hx) (hz hx)
  | smul c y _ hy =>
    rw [Algebra.smul_def, mul_assoc]
    exact mul_mem (intE_coe D c) (hy hx)

theorem one_mem_pairSpan (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    (1 : D.host.E) ∈ pairSpan D (bInv D cc r) := by
  have h₁ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).2
  have h₂ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  have hm := Submodule.mul_mem_mul h₁ h₂
  rw [Submodule.span_mul_span] at hm
  set c : D.host.E := r * D.host.conj r / (Ideal.absNorm cc : D.host.E) ^ 2 with hc
  have hle : Submodule.span (𝓞 D.host.E) ({t | ∃ α ∈ cE D cc, ∃ β ∈ cE D cc, t = D.host.conj α * β} *
      {t | ∃ α ∈ cE D D.host.ccK, ∃ β ∈ cE D D.host.ccK, t = D.host.conj α * β}) ≤
      (pairSpan D (bInv D cc r)).comap (LinearMap.mulLeft (𝓞 D.host.E) c) := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, ε, hε, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨r * D.host.conj α * ε / (Ideal.absNorm cc : D.host.E), ?_,
      r * D.host.conj β * γ / (Ideal.absNorm cc : D.host.E), ?_, ?_⟩
    · unfold bInv; exact Submodule.subset_span ⟨α, hα, ε, hε, rfl⟩
    · unfold bInv; exact Submodule.subset_span ⟨β, hβ, γ, hγ, rfl⟩
    · simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj, hc]
      field_simp
  have h := hle hm
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h
  convert h using 1
  unfold GlobalTheory.NormExact.IsScale at hs
  rw [hc]
  field_simp
  linear_combination -hs

theorem mem_of_dual (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) {y : D.host.E}
    (hy : ∀ x ∈ bInv D cc r, IntE D (y * D.host.conj x)) : y ∈ bInv D cc r := by
  have hle : pairSpan D (bInv D cc r) ≤ (bInv D cc r).comap (LinearMap.mulLeft (𝓞 D.host.E) y) := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    obtain ⟨o, ho⟩ := hy x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have : y * (u * D.host.conj x) = o • u := by rw [Algebra.smul_def, ho]; ring
    rw [this]
    exact Submodule.smul_mem _ o hu
  have h := hle (one_mem_pairSpan D cc r hn hs)
  simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] using h

theorem exists_ne_zero (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    ∃ x ∈ bInv D cc r, x ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hle : pairSpan D (bInv D cc r) ≤ ⊥ := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    simp [hne u hu]
  have h := hle (one_mem_pairSpan D cc r hn hs)
  rw [Submodule.mem_bot] at h
  exact one_ne_zero h

theorem lsB_sd (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) (hcc : cc ≠ ⊥)
    (hs : GlobalTheory.NormExact.IsScale D cc r) : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r a) := by
  have hn : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hcc)
  have hsingle : ∀ (i : Fin a) (u : D.host.E), u ∈ bInv D cc r → (Pi.single i u : Fin a → D.host.E) ∈ lsB D cc r a := by
    intro i u hu
    rw [mem_lsB]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hu
    · simp only [Pi.single_apply, hj, if_false]; exact zero_mem _
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, hne⟩ := exists_ne_zero D cc r hn hs
    have hcne : D.host.conj x₀ ≠ 0 := (map_ne_zero_iff _ D.host.conj.injective).mpr hne
    let M := Submodule.span (𝓞 D.host.E)
      (Set.range fun i : Fin a => (Pi.single i (D.host.conj x₀)⁻¹ : Fin a → D.host.E))
    have hM : M.FG := Submodule.fg_span (Set.finite_range _)
    haveI := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    intro y hy
    rw [mem_lsB] at hy
    rw [pi_eq_sum_univ' y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := intE_mul_conj D cc r hn hs (hy i) hx₀
    have he : y i • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) = o • Pi.single i (D.host.conj x₀)⁻¹ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def, ho]
        field_simp
      · simp [Pi.single_apply, hj]
    rw [he]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro v _
    have he : ∀ i : Fin a, (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
        Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
      intro i
      have key : ∀ t ∈ pairSpan D (bInv D cc r), t • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
          Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
        intro t ht
        unfold pairSpan at ht
        induction ht using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨u, hu, x, hx, rfl⟩ := hg
          have hg' : (u * D.host.conj x) • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) =
              D.host.conj x • Pi.single i u := by
            funext j
            by_cases hj : j = i
            · subst hj; simp [mul_comm]
            · simp [Pi.single_apply, hj]
          rw [hg']
          exact Submodule.smul_mem _ _ (Submodule.subset_span (hsingle i u hu))
        | zero => rw [zero_smul]; exact zero_mem _
        | add s t _ _ hs' ht' => rw [add_smul]; exact add_mem hs' ht'
        | smul c t _ ht' => rw [smul_assoc]; exact Submodule.smul_of_tower_mem _ c ht'
      simpa using key 1 (one_mem_pairSpan D cc r hn hs)
    rw [pi_eq_sum_univ' v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  · intro y
    rw [mem_lsB]
    constructor
    · intro hy x hx
      rw [mem_lsB] at hx
      rw [intE_iff]
      unfold hE
      exact Subring.sum_mem _ fun i _ => intE_mul_conj D cc r hn hs (hy i) (hx i)
    · intro h i
      refine mem_of_dual D cc r hn hs fun x hx => ?_
      have h' := h (Pi.single i x) (hsingle i x hx)
      unfold hE at h'
      rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
        Pi.single_eq_same] at h'

end GlobalTheory.VacRead.SelfDual

theorem GlobalTheory.VacRead.lsB_selfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) :=
  fun D cc r a hcc hs => GlobalTheory.VacRead.SelfDual.lsB_sd D cc r a hcc hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLatticeStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)), Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val := by
  first | exact @GlobalTheory.StdRead.isIntM_of_isFrame_stdL | exact GlobalTheory.StdRead.isIntM_of_isFrame_stdL | (intros; apply GlobalTheory.StdRead.isIntM_of_isFrame_stdL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegularStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularSemisimpleUnitaryData_of_regular : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular D.sp.cm.sig V.gram γ.1 := by
  first | exact @GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | exact GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | (intros; apply GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS <;> assumption)
end

