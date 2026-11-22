import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslateStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_frames_move_integralRightTranslate : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  first | exact @GlobalTheory.FrameShift.exists_pt_mul | exact GlobalTheory.FrameShift.exists_pt_mul | (intros; apply GlobalTheory.FrameShift.exists_pt_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPointFrames_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
        (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P))) := by
  first | exact @GlobalTheory.RatFrame.frame_rat | exact GlobalTheory.RatFrame.frame_rat | (intros; apply GlobalTheory.RatFrame.frame_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointLeftTranslateRationalUnitary
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem ratPt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi β x x' p γ hγ hx hp
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹) (GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form D _ _ _ (hP.crd_orth i hi) hγ)
  have hmv : ∀ y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ratA D.host.F (A.crd i hi) * (ratA D.host.F γ * y) = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * y) := by
    intro y
    rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_right]
  let a' : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K)) := (g, 1, 1)
  refine ⟨a' • p, ?_, ?_, ?_⟩
  · have e1 : (a' • p).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
    rw [e1, GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage, hg, hp.lat, hx, latCo_rat _ _ _ hγ]
  · intro P
    have hb := hp.frame P
    rw [hx, hmv, mul_assoc (ratA D.host.F (seamGL t.seam g.1))]
    by_cases hPg : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hPg
      have e0 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = ((g, (1 : GLG t.X.E (D.R.N i) t.Pr.vGs)) • p.deco).1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      rw [hD, e0] at hb
      rw [hD, e1]
      exact GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one t.seam p.deco ⟨P.1, hPg⟩ g (mq_rowSG_unif (t.tup μ) hP.fields.ok t.pr_ok hP.sel P) _ hb
    · have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
        unfold frsF
        rw [dif_neg hPg, dif_neg hPg]
        show g.1 * p.fr _ * (((1 : GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) _)⁻¹).1 = _
        simp
      rw [e1, map_mul, nearAt_rat_mul]
      exact hb
  · intro P v h hv
    rw [hx, hmv]
    exact GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)

end GlobalTheory.TwRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsFramesCongrAwayFromBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.AwayFr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_of_prV_eq (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v Q) (n : ℕ)
    (y y₁ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y) :
    GlobalTheory.TwU.CongAt Q n (y⁻¹ * y₁) := by
  intro a b
  apply GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero F E v Q hv
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := E) v) (y⁻¹ * y₁) = 1 := by
    rw [map_mul, h, map_inv, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin N) (TensorProduct F E (v.adicCompletion F)) => (g : Matrix (Fin N) (Fin N) (TensorProduct F E (v.adicCompletion F))) a b) h1
  have h3 : Formalism.UG.prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b) =
      (1 : Matrix (Fin N) (Fin N) (TensorProduct F E (v.adicCompletion F))) a b := h2
  rw [Matrix.sub_apply, map_sub, h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem congAt_ratA_of_near (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v Q) (n : ℕ)
    (hn : 1 ≤ n) (y y₁ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (g g₁ : GL (Fin N) E)
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y)
    (hg : GlobalTheory.TwU.NearAt Q n y g) (hg₁ : GlobalTheory.TwU.NearAt Q n y₁ g₁) :
    GlobalTheory.TwU.CongAt Q n (GlobalTheory.TwU.ratA F (g⁻¹ * g₁)) := by
  have e : GlobalTheory.TwU.ratA F (g⁻¹ * g₁) = (y⁻¹ * GlobalTheory.TwU.ratA F g)⁻¹ * ((y⁻¹ * y₁) * (y₁⁻¹ * GlobalTheory.TwU.ratA F g₁)) := by
    rw [map_mul, map_inv]; group
  rw [e]
  exact GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both F E Q n N _ _ (GlobalTheory.T.adelicMatrixCongruentOneAtPrime_inv_of_pos_depth F E Q n N _ hn hg) (GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both F E Q n N _ _ (congAt_of_prV_eq v Q hv n y y₁ h) hg₁)

end GlobalTheory.AwayFr

namespace GlobalTheory.AwayFr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

theorem monoidHom_mul_mul_congr_middle {M M' : Type} [Monoid M] [Monoid M'] (φ : M →* M') (a b b₁ c : M) (h : φ b₁ = φ b) :
    φ (a * b₁ * c) = φ (a * b * c) := by
  rw [map_mul, map_mul, h, ← map_mul, ← map_mul]

theorem intAt_of_cong {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z δ : E) (hδ : IntAt P δ)
    (h : IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (z - δ))) : IntAt P z := by
  have e : z = δ + (((qOf P ^ n : ℕ) : ℕ) : E) * ((((qOf P : ℕ) : E) ^ n)⁻¹ * (z - δ)) := by
    rw [← mul_assoc, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ (GlobalTheory.TopInv.qOf_ne P)), one_mul]; ring
  rw [e]
  exact hδ.add ((GlobalTheory.TopInv.intAt_nat (P := P) (qOf P ^ n)).mul h)

theorem intAt_single {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (s l : Fin n) :
    IntAt P ((Pi.single s 1 : Fin n → E) l) := by
  rw [Pi.single_apply]
  split_ifs
  · simpa using GlobalTheory.TopInv.intAt_nat (P := P) 1
  · simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0

theorem intAt_of_seam {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E)
    (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
  · rwa [← mem_seamP s P, RingEquiv.apply_symm_apply]
  · apply s.iE.injective
    have k : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E ((RingOfIntegers.mapRingEquiv s.iE).symm w)) = algebraMap _ _ w := by
      intro w
      conv_rhs => rw [← RingEquiv.apply_symm_apply (RingOfIntegers.mapRingEquiv s.iE) w]
      rfl
    rw [map_mul, k, k, e]

theorem mem_stdAt_of_int {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g : Sp E n ≃ₗ[E] Sp E n) (hg : ∀ s l, IntAt P (g (Pi.single s 1) l)) (w : Sp E n) (hw : w ∈ stdAt E n P) :
    g w ∈ stdAt E n P := by
  rw [stdAt, mem_localization_standardLattice] at hw ⊢
  intro l
  have e : g w l = ∑ s, g (Pi.single s 1) l * w s := by
    have := congrFun (LinearMap.toMatrix'_mulVec g.toLinearMap w) l
    rw [← LinearEquiv.coe_toLinearMap, ← this]
    simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, LinearEquiv.coe_toLinearMap]
  rw [e]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => ha.add hb) (by simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0)
    fun s _ => (hg s l).mul (hw s)

end GlobalTheory.AwayFr

namespace GlobalTheory.AwayFr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

theorem frames_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P
  classical
  have hSS := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1
  have hQ : seamP t.seam P.1 ∈ ssRec t u μ :=
    (mem_ssRec t u μ P.1).2 (by rw [hSS]; exact Finset.mem_union_right _ P.2)
  have hv : IsOver (underPl D.host.F (seamP t.seam P.1)) (seamP t.seam P.1) := rfl
  have hxv := hx _ ⟨_, hQ, hv⟩
  have hD : 1 ≤ (t.cst μ).D P := ((t.idx_ok μ).cst_ok).D_pos P
  have c1 := congAt_ratA_of_near _ _ hv _ hD _ _ _ _ (monoidHom_mul_mul_congr_middle _ _ _ _ _ hxv) (hp.frame P) (hp₁.frame P)
  have c2 := congAt_ratA_of_near _ _ hv _ hD _ _ _ _ (monoidHom_mul_mul_congr_middle _ _ _ _ _ hxv.symm) (hp₁.frame P) (hp.frame P)
  rw [← map_inv, ← map_mul] at c1 c2
  have i1 := GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent _ _ _ _ _ _ c1
  have i2 := GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent _ _ _ _ _ _ c2
  rw [GlobalTheory.T.residueCard_columnFieldPrimeToHostPrime_eq] at i1 i2
  have entry : ∀ (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (l s : Fin (D.R.N j)),
      ((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s =
        t.seam.iE (g (Pi.single s 1) l) := by
    intro g l s
    show ((LinearMap.toMatrix' g.toLinearMap).map (t.seam.iE : t.X.E →+* D.host.E)) l s = _
    rw [Matrix.map_apply, LinearMap.toMatrix'_apply]
    rfl
  have cong : ∀ g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j),
      (∀ l s : Fin (D.R.N j), IntAt (seamP t.seam P.1) ((((qOf P.1 : ℕ) : D.host.E) ^ (t.cst μ).D P)⁻¹ *
        (((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s -
          (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s))) →
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (g (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l)) := by
    intro g h s l
    apply intAt_of_seam t.seam P.1
    have := h l s
    rw [entry, Matrix.one_apply] at this
    convert this using 1
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, Pi.single_apply]
    split_ifs <;> simp
  have h1 := cong ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) (by simpa only [map_mul, map_inv] using i1)
  have h2 := cong ((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (by simpa only [map_mul, map_inv] using i2)
  have int1 : ∀ s l, IntAt P.1 (((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) (Pi.single s 1) l) := fun s l =>
    intAt_of_cong P.1 _ _ _ (intAt_single P.1 s l) (h1 s l)
  have int2 : ∀ s l, IntAt P.1 (((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (Pi.single s 1) l) := fun s l =>
    intAt_of_cong P.1 _ _ _ (intAt_single P.1 s l) (h2 s l)
  have hk : (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P ∈ GLint t.X.E (D.R.N j) P.1 := by
    intro w
    constructor
    · intro hw
      have e : w = ((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) w) := by
        rw [← LinearEquiv.mul_apply, mul_assoc, mul_inv_cancel_left, inv_mul_cancel]
        rfl
      rw [e]
      exact mem_stdAt_of_int P.1 _ int2 _ hw
    · exact mem_stdAt_of_int P.1 _ int1 w
  exact ⟨⟨(frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P, hk⟩, by simp, h1⟩

end GlobalTheory.AwayFr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem dualL_fg {n : ℕ} (τ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M) : (dualL τ J M).FG := by
  classical
  obtain ⟨S, hS⟩ := hM.fg
  have hSE : Submodule.span E ((S : Set (Fin n → E))) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 E) E, hS]
    exact hM.span_eq_top
  let Θ : (Fin n → E) →ₗ[𝓞 E] (S → E) :=
    { toFun := fun y s => hform τ J s.1 y
      map_add' := fun y y' => by
        funext s
        simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r y => by
        funext s
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [show r • y = (r : E) • y from (algebraMap_smul E r y).symm, GlobalTheory.LevelHecke.DualConj.hform_smul_right,
          Algebra.smul_def] }
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ x ∈ Submodule.span E (S : Set (Fin n → E)), hform τ J x y = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact congrFun hy ⟨x, hx⟩
      | zero => simp [hform]
      | add x x' _ _ hx hx' =>
        have e : hform τ J (x + x') y = hform τ J x y + hform τ J x' y := by
          simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        rw [e, hx, hx', add_zero]
      | smul c x _ hx => rw [GlobalTheory.LevelHecke.DualConj.hform_smul_left, hx, mul_zero]
    have hJy : J *ᵥ y = 0 := by
      funext i
      have := h0 (Pi.single i 1) (by rw [hSE]; trivial)
      show (J *ᵥ y) i = 0
      rw [← this]
      simp [hform, Pi.single_apply, Matrix.mulVec, dotProduct]
    have : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [this, hJy, Matrix.mulVec_zero]
  let P : Submodule (𝓞 E) (S → E) := LinearMap.range
    (LinearMap.pi fun s : S => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj s) : (S → 𝓞 E) →ₗ[𝓞 E] (S → E))
  have hP : P.FG := by
    show (LinearMap.range _).FG
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  refine Submodule.fg_of_fg_map_injective Θ hΘ (Submodule.FG.of_le_of_isNoetherian (T := P) ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (GlobalTheory.LevelHecke.DualConj.mem_dualL τ J M y).1 hy
  choose f hf using fun s : S => hy' s.1 (hS ▸ Submodule.subset_span s.2)
  refine ⟨f, ?_⟩
  funext s
  exact hf s

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_sup_smul_iff (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M N : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E)
    (z : Fin n → E ⊗[F] v.adicCompletion F) :
    z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (M ⊔ Ideal.span {a} • N) ↔
      ∃ m ∈ latS (F := F) (v.adicCompletion F) (intV E v) M, ∃ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
        z = m + inclE (F := F) (v.adicCompletion F) (a : E) • w := by
  set c := inclE (F := F) (v.adicCompletion F) (a : E) with hc
  have hincl : ∀ y y' : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((y + y') i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (y i)) + fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    intro y y'; funext i; simp
  have hsm : ∀ y : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((a • y) i)) =
      c • fun i => inclE (F := F) (v.adicCompletion F) (y i) := by
    intro y; funext i
    simp only [Pi.smul_apply, smul_eq_mul, hc, ← map_mul]
    rw [Algebra.smul_def]
  have hcw : ∀ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
      c • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Ideal.span {a} • N) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← hsm]
      exact Submodule.subset_span ⟨a • y, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add w w' _ _ hw hw' => rw [smul_add]; exact add_mem hw hw'
    | smul s w _ hw =>
      rw [Subring.smul_def, smul_comm]
      exact Submodule.smul_mem _ s hw
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Submodule.ideal_span_singleton_smul] at hq
      obtain ⟨q', hq', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
      exact ⟨_, Submodule.subset_span ⟨p, hp, rfl⟩, _, Submodule.subset_span ⟨q', hq', rfl⟩, by
        show (fun i => inclE (F := F) (v.adicCompletion F) ((p + a • q') i)) = _
        rw [hincl, hsm]⟩
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      obtain ⟨m', hm', w', hw', rfl⟩ := hz'
      exact ⟨m + m', add_mem hm hm', w + w', add_mem hw hw', by rw [smul_add]; abel⟩
    | smul s z _ hz =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      refine ⟨s • m, Submodule.smul_mem _ s hm, s • w, Submodule.smul_mem _ s hw, ?_⟩
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rintro ⟨m, hm, w, hw, rfl⟩
    have h1 : (M : Set (Fin n → E)) ⊆ ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_left
    have h2 : ((Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ⊆
        ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_right
    exact add_mem (Submodule.span_mono (Set.image_mono h1) hm) (Submodule.span_mono (Set.image_mono h2) (hcw w hw))

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

theorem isLattice_compan {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (M : Submodule (𝓞 E) (Fin N → E)) (hM : Submodule.IsLattice E M) :
    Submodule.IsLattice E (compan (sp := sp) J a M) := by
  refine ⟨?_, ?_⟩
  · exact hM.fg.sup ((Submodule.FG.smul (IsNoetherian.noetherian (Ideal.span {a})) (dualL_fg (sp.cm.sig : E →+* E) J hJ M hM)))
  · rw [eq_top_iff, ← hM.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)

theorem compan_latAd_eq {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = sp.cm.sig) (J : Matrix (Fin N) (Fin N) E)
    (hJ : IsUnit J.det) (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    compan (sp := sp) J a (latAd x Lb) = latAd x (compan (sp := sp) J a Lb) := by
  have hcomp : ∀ M : Submodule (𝓞 E) (Fin N → E),
      compan (sp := sp) J a M = M ⊔ Ideal.span {a} • dualL (σ : E →+* E) J M := by
    intro M
    unfold compan dualL
    rw [hσ]
  have hLb : Submodule.IsLattice E Lb := ⟨hfg, hspan⟩
  have hfin : Module.Finite (𝓞 E) Lb := Module.Finite.iff_fg.mpr hfg
  have hlatAd : ∀ M : Submodule (𝓞 E) (Fin N → E), Submodule.IsLattice E M → Submodule.IsLattice E (latAd x M) := by
    intro M hM
    have e : latAd x M = Formalism.UG.CS.globLat x M := Submodule.span_eq (Formalism.UG.CS.globLat x M)
    rw [e]
    exact Formalism.UG.P.csGlob_lattice M (Module.Finite.iff_fg.mpr hM.fg) hM.span_eq_top x
  have hΛ := hlatAd Lb hLb
  have hcL := isLattice_compan sp J hJ a Lb hLb
  have hcΛ := isLattice_compan sp J hJ a (latAd x Lb) hΛ
  have hRHS := hlatAd _ hcL
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (compan (sp := sp) J a (latAd x Lb)) ↔
        z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x (compan (sp := sp) J a Lb)) := by
    intro v z
    set g := bc (prV (E := E) v) x with hg
    have hgU : g ∈ UPts σ J (v.adicCompletion F) := GlobalTheory.MemDual.bc_prV_mem_UPts σ J v hx
    have hcar1 := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v
    have hcar2 := GlobalTheory.LocCarry.mem_latS_latAd_iff x (compan (sp := sp) J a Lb)
      (Module.Finite.iff_fg.mpr hcL.fg) hcL.span_eq_top v
    have hdm := GlobalTheory.DualCompletion.dual_move F E σ N J v (latAd x Lb) Lb g hJ hΛ hLb hgU hcar1
    have hgg : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, ((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ
        ((g : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hgg' : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, (g : Matrix (Fin N) (Fin N) _) *ᵥ
        (((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hcar2, hcomp, hcomp, mem_latS_sup_smul_iff, mem_latS_sup_smul_iff]
    constructor
    · rintro ⟨m, hm, w, hw, rfl⟩
      exact ⟨_, (hcar1 m).1 hm, _, (hdm w).1 hw, by rw [Matrix.mulVec_add, Matrix.mulVec_smul]⟩
    · rintro ⟨m, hm, w, hw, he⟩
      refine ⟨(g : Matrix (Fin N) (Fin N) _) *ᵥ m, (hcar1 _).2 (by rw [hgg]; exact hm),
        (g : Matrix (Fin N) (Fin N) _) *ᵥ w, (hdm _).2 (by rw [hgg]; exact hw), ?_⟩
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← he, hgg']
  apply le_antisymm
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hRHS.fg) hRHS.span_eq_top w fun v => ?_
    exact (key v _).1 (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hcΛ.fg) hcΛ.span_eq_top w fun v => ?_
    exact (key v _).2 (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem locP_companion_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  intro R F E _ _ _ _ _ _ sp N σ hσ J hJ a x hx Lb hfg hspan P
  rw [compan_latAd_eq sp σ hσ J hJ a x hx Lb hfg hspan]

end GlobalTheory.CompanLatAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  first | exact @GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | exact GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | (intros; apply GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousDefiniteThetaIntegralVectorFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm : ∀ {D : D7} (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    IsWeilDatumO ψ V W χS χT om → (∀ τ, (gramAt D V τ).PosDef) →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO V W → ℂ)),
    (∀ x, IsThetaFunO ψ V W (L x)) → ∀ u : GA D V → X, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) →
    Continuous (fun g => ∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν) := by
  first | exact @GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector | exact GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector | (intros; apply GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelKeepsBaseCosetStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupledStepChartLevel_keeps_baseCoset : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∀ P (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P ((κ'' P).1 y) (A.y0 β' P) ↔
      SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 β' P)) := by
  first | exact @GlobalTheory.CplCoset.sameCoset_kappa | exact GlobalTheory.CplCoset.sameCoset_kappa | (intros; apply GlobalTheory.CplCoset.sameCoset_kappa <;> assumption)
end

