import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionMetricCompatStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_composition_metric_compat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → h.IsCInf → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y + Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y = Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y + Met.bcDens (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  first | exact @GlobalTheory.CurveDens.bcDens_add_bcDens_stage | exact GlobalTheory.CurveDens.bcDens_add_bcDens_stage | (intros; apply GlobalTheory.CurveDens.bcDens_add_bcDens_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignForWeilModelFamily
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DatumFourier

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vec_eq_sum_heis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ (s : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) s (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) f₀ f → f = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) f₀ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he s f₀ f hf => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hf
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

open GlobalTheory.AdTh.MovedDatum in

theorem vec_eq_sum_roots : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad 1 → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) 1)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι 1 mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) 1)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → ∀ (s : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) s (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) f₀ f → f = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) f₀ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := vec_eq_sum_heis D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu s f₀ f hf => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨-, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPair.isPair_record D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := hf.1
  refine (hδ t l φ hφ hP e he s f₀ f hf).trans ?_
  congr 1
  refine finsum_congr fun q => ?_
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hV.1 (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨k, hk⟩ : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
      rw [hk, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N 1 1 Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s
      fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h0 : ∀ x : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) 1 1 x = x := fun x => by
    rw [actO, inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, Matrix.one_mul]
  rw [h0, h0] at h1 h2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • c) f₀ = f₀ := hvac.lat.1 c hc
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ f₀ |>.trans (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.DatumFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem isThPVecOf_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT Pg Q ξ ξ' f₀ f}
    (hQ : Q = ∅) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f := by
  subst hQ
  have e : ∀ y, omegaQ (a := T.rank) (b := S.rank) ∅ T.rank ξ' (-1) y = omegaQ ∅ T.rank ξ (-1) y := fun y => by
    simp [omegaQ]
  unfold IsThPVecOf at h ⊢
  simp only [e]
  exact h

open GlobalTheory.OneMapRef.FinDatum in

theorem vec_eq_mean_translates : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∃ ε : ℤˣ, ∀ (s : Fam (Wc D i)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) s (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg ∅ (fun _ => 1) f₀ f → ∀ (k : O.Cl' ()) (N : ℕ), 0 < N → (O.dδ ()).l₂.M ∣ N → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ ()).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1)) N Y → f = ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : ℕ) : ℂ)⁻¹ • ∑ᶠ q, inC O.c' (O.w () k q) • heisO R.ψ (Vc D i) (Wc D i) (finR (Vc D i) (rank_Wc i) (-(Y q))) f₀ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP
  have hstd : VStd D i := hP.lift.std
  obtain ⟨hι, hiso⟩ := lat_iotaW T tie.laws i
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourier.vec_eq_sum_roots D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso
  refine ⟨-δ, fun s f₀ f hf k N _ hN Y hY => ?_⟩
  have hQ0 : R.Q A.μ0 = ∅ := (chars_of_lift D G Pl0 T0 A _ R F hR i).2.2.1
  have hw : ∀ q, inC O.c' (O.w () k q) = GlobalTheory.AdTh.hatC (O.dδ ()).l₂ (fun x => inC O.c' (O.φ () x)) q := fun q =>
    (congrArg (inC (O.dδ ()).c₂) (hP.w () k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ ()).c₂ _ q)
  have hφ : PhiIs R i (RingHom.id ℂ) A.μ0 (iotaW T i) (Mfr (O.dδ ()).l₂ • ⊤) fun x => inC O.c' (O.φ () x) :=
    (hP.tuple ()).phi
  obtain ⟨h1, h2, h3⟩ := (hP.tuple ()).half
  have hMb : (O.dδ ()).l₂.Mb = T.Q.l.Mb * (O.dδ ()).I := (hP.cov ()).1.2.2.2.1
  have hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q A.μ0 → (O.dδ ()).l₂.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h =>
    ⟨by
      rw [hMb]
      exact h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h =>
        Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩
  have hY' := isRoots_sign (-δ) hN hY
  have hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1)) := by
    rw [← hι.2]
    exact latR_range _ _
  rw [← hL] at hY'
  have h := hδ A.μ0 (O.dδ ()).l₂ _ hφ hl 0 (O.dδ ()).l₂.M ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1))
    (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩
    ⟨(O.dδ ()).l₂.odd, dvd_rfl, le_inf Submodule.smul_le_right Submodule.smul_le_right⟩ ?_ _
    (fun q => ((-(Y q)).submatrix id (Fin.cast (rank_Wc i)))ᵀ) (fun q => finR (Vc D i) (rank_Wc i) (-(Y q))) hY' ?_
    s f₀ f (isThPVecOf_empty hQ0 hf)
  · simp only [hw]
    exact h
  · intro v
    rw [show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]
    refine ⟨mem_std_star T.Q.H v, fun h => ?_⟩
    have h' := mem_std_star T.Q.H _ h
    simp only [star_star] at h'
    exact h'
  · intro a _
    refine ⟨0, zero_mem _, ?_⟩
    rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
    exact sub_self _
  · intro q
    refine ⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩
    rw [smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]

end GlobalTheory.GalOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDeriv
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem slice_word_fderivs (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type)
    [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)))
    (vs : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y))) := by
  induction vs with
  | nil => exact ⟨rfl, hΦ⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd : Differentiable ℝ (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [h1]; exact h2.differentiable (by simp)
    refine ⟨?_, ?_⟩
    · funext x
      simp only [List.map_cons, List.foldr_cons]
      rw [word_cons, GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase F κ ψ ℓ hψ _ y hd (v, 0) x, h1]
      simp
    · simp only [List.foldr_cons]
      exact (h2.fderiv_right (by simp)).clm_apply contDiff_const

theorem slice_word_mul_fderivs : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hΦ u i vs x
  obtain ⟨h1, h2⟩ := slice_word_fderivs F κ ψ ℓ hψ Φ y hΦ vs
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) := by
    let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
      ℓ ∘ₗ ∑ k, (LinearMap.mulRight ℝ (u k)) ∘ₗ LinearMap.proj k
    have hLe : (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) = L := by
      funext x; simp [L, LinearMap.sum_apply]
    rw [hLe]
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => 2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hL)
  suffices H : ∀ i : ℕ,
      (fun x => word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) by
    exact congrFun (H i).1 x
  intro i
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · funext x; simp only [List.replicate_zero, List.nil_append, pow_zero, one_mul]; exact congrFun h1 x
    · simpa using h2
  | succ i ih =>
    obtain ⟨e1, e2⟩ := ih
    have hd : Differentiable ℝ (fun x =>
        word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [e1]; exact e2.differentiable (by simp)
    refine ⟨?_, (hc.pow (i + 1)).mul h2⟩
    funext x
    rw [List.replicate_succ, List.cons_append, word_cons, GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase F κ ψ ℓ hψ _ y hd (0, u) x]
    have e1x := congrFun e1 x
    simp only [ContinuousLinearMap.map_zero, zero_add, e1x]
    ring

end GlobalTheory.WeilL2Words
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
section
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.WeilIntegral

set_option autoImplicit false in
open scoped TensorProduct in

theorem _root_.GlobalTheory.WeilIntegral.isAlgebraic_of_etale (S B : Type) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (f : B) : IsAlgebraic S f := by
  classical
  let K := FractionRing S
  haveI : Algebra.Etale K (TensorProduct S K B) := Algebra.Etale.baseChange S B K
  haveI : Module.Finite K (TensorProduct S K B) :=
    Algebra.FormallyUnramified.finite_of_free K (TensorProduct S K B)
  haveI hal : Algebra.IsAlgebraic K (TensorProduct S K B) := Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp0, hp⟩ := hal.isAlgebraic ((1 : K) ⊗ₜ[S] f)
  set q := IsLocalization.integerNormalization (nonZeroDivisors S) p
  have hq0 : q ≠ 0 := fun h0 =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h0)
  have hq : Polynomial.aeval ((1 : K) ⊗ₜ[S] f) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p hp
  have hmap : (1 : K) ⊗ₜ[S] Polynomial.aeval f q = 0 := by
    rw [← hq, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 (TensorProduct.isBaseChange S B K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) (TensorProduct.mk S K B 1)).1 hmap
  refine ⟨Polynomial.C (s : S) * q, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hq0
  · rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]
    exact hs

theorem exists_eq_C_mul_coeff_one {O σ : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    (a : MvPolynomial σ O) (ha : a ≠ 0) :
    ∃ (c : O) (a' : MvPolynomial σ O) (d : σ →₀ ℕ), c ≠ 0 ∧ a = MvPolynomial.C c * a' ∧ a'.coeff d = 1 := by
  classical
  have key : ∀ s : Finset (σ →₀ ℕ), s.Nonempty → ∃ d ∈ s, ∀ e ∈ s, a.coeff d ∣ a.coeff e := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton x => exact ⟨x, by simp, by simp⟩
    | cons x s hx hs ih =>
      obtain ⟨d, hd, h⟩ := ih
      rcases ValuationRing.dvd_total (a.coeff d) (a.coeff x) with h1 | h1
      · refine ⟨d, by simp [hd], fun e he => ?_⟩
        rcases Finset.mem_cons.1 he with rfl | he
        · exact h1
        · exact h e he
      · refine ⟨x, by simp, fun e he => ?_⟩
        rcases Finset.mem_cons.1 he with rfl | he
        · exact dvd_rfl
        · exact h1.trans (h e he)
  obtain ⟨d, hd, h⟩ := key a.support (MvPolynomial.support_nonempty.2 ha)
  have hc : a.coeff d ≠ 0 := MvPolynomial.mem_support_iff.1 hd
  have hdvd : MvPolynomial.C (a.coeff d) ∣ a := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro e
    by_cases he : e ∈ a.support
    · exact h e he
    · rw [MvPolynomial.notMem_support_iff.1 he]
      exact dvd_zero _
  obtain ⟨a', ha'⟩ := hdvd
  refine ⟨a.coeff d, a', d, hc, ha', ?_⟩
  have := congrArg (MvPolynomial.coeff d) ha'
  rw [MvPolynomial.coeff_C_mul] at this
  exact mul_left_cancel₀ hc (by rw [← this, mul_one])

theorem exists_prime_dvd_of_etale {O B : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing B]
    [IsDomain B] [Algebra O B] {n : ℕ} (φ : MvPolynomial (Fin n) O →ₐ[O] B) (hφ : φ.Etale) (f : B) (hf : f ≠ 0)
    (q : Ideal B) [q.IsPrime] :
    ∃ (q' : Ideal B) (g : B) (c : O), q'.IsPrime ∧ (∀ x : O, algebraMap O B x ∈ q → algebraMap O B x ∈ q') ∧
      g ∉ q' ∧ c ≠ 0 ∧ f ∣ algebraMap O B c * g := by
  let S := MvPolynomial (Fin n) O
  letI : Algebra S B := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale S B := hφ
  have hφ' : ∀ x : S, algebraMap S B x = φ x := fun _ => rfl
  obtain ⟨a, ha, hfa⟩ := (isAlgebraic_of_etale S B f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
  obtain ⟨c, a', d, hc, rfl, hd⟩ := exists_eq_C_mul_coeff_one a ha
  let P : Ideal O := q.comap (algebraMap O B)
  let P₀ : Ideal S := RingHom.ker (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk P))
  haveI : P₀.IsPrime := RingHom.ker_isPrime _
  have hle : P₀ ≤ q.under S := by
    simp only [P₀]
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
    intro x hx
    change φ (MvPolynomial.C x) ∈ q
    rw [MvPolynomial.algHom_C]
    exact hx
  haveI : Module.Flat S B := Algebra.Smooth.flat S B
  haveI : Algebra.HasGoingDown S B := Algebra.HasGoingDown.of_flat
  obtain ⟨q', -, hq', hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P₀) (q := q.under S) q hle
  have hmem : ∀ x : S, x ∈ P₀ ↔ φ x ∈ q' := fun x => Ideal.mem_of_liesOver q' P₀ x
  refine ⟨q', φ a', c, hq', fun x hx => ?_, fun h => ?_, hc, ?_⟩
  · rw [← MvPolynomial.algHom_C φ, ← hmem, RingHom.mem_ker, MvPolynomial.map_C,
      Ideal.Quotient.eq_zero_iff_mem.2 (show x ∈ P from hx), map_zero]
  · have h0 := congrArg (MvPolynomial.coeff d) (RingHom.mem_ker.1 ((hmem a').2 h))
    rw [MvPolynomial.coeff_map, hd, map_one, MvPolynomial.coeff_zero] at h0
    exact one_ne_zero h0
  · rw [hφ', map_mul, MvPolynomial.algHom_C] at hfa
    exact hfa

theorem specialFibreNotInClosure_of_valuationRing (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] : SpecialFibreNotInClosure p O := by
  rintro R _ _ _ _ f hf ⟨q, hq⟩
  obtain ⟨h, hh, hs⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth O q.asIdeal
  let B := Localization.Away h
  have hh0 : h ≠ 0 := fun e => hh (e ▸ q.asIdeal.zero_mem)
  have hpow : Submonoid.powers h ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hh0
  haveI : IsDomain B := IsLocalization.isDomain_localization hpow
  have hinj : Function.Injective (algebraMap R B) := IsLocalization.injective B hpow
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension O B :=
    P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial P.dimension O B
  have hdisj : Disjoint (Submonoid.powers h : Set R) q.asIdeal := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI : (q.asIdeal.map (algebraMap R B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers h) _ _ q.isPrime hdisj
  obtain ⟨q', g, c, hq', hq'', hg, hc, b, hb⟩ := exists_prime_dvd_of_etale φ hφ (algebraMap R B f)
    (fun e => hf (hinj (by rw [e, map_zero]))) (q.asIdeal.map (algebraMap R B))
  obtain ⟨⟨g₀, s⟩, hgs⟩ := IsLocalization.surj (Submonoid.powers h) g
  obtain ⟨⟨b₀, t⟩, hbt⟩ := IsLocalization.surj (Submonoid.powers h) b
  simp only at hgs hbt
  have hs' : algebraMap R B s ∉ q' := fun e =>
    hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ e (IsLocalization.map_units B s))
  have ht' : algebraMap R B t ∉ q' := fun e =>
    hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ e (IsLocalization.map_units B t))
  refine ⟨⟨q'.comap (algebraMap R B), Ideal.comap_isPrime _ _⟩, g₀ * t, c, ?_, ?_, hc, b₀ * s, hinj ?_⟩
  · have := hq'' p (by simpa using Ideal.mem_map_of_mem (algebraMap R B) hq)
    simpa [Ideal.mem_comap] using this
  · change algebraMap R B (g₀ * t) ∉ q'
    rw [map_mul, ← hgs]
    exact hq'.mul_notMem (hq'.mul_notMem hg hs') ht'
  · simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply, ← hgs, ← hbt]
    linear_combination (algebraMap R B s * algebraMap R B t) * hb

theorem specialFibreNotInClosure (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) : SpecialFibreNotInClosure p O := by
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  exact specialFibreNotInClosure_of_valuationRing p O

end GlobalTheory.WeilIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinatesStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  first | exact @GlobalTheory.RealCharF.psi_symplOHF_iotaVF | exact GlobalTheory.RealCharF.psi_symplOHF_iotaVF | (intros; apply GlobalTheory.RealCharF.psi_symplOHF_iotaVF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassCountCharPolyStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.twisted_class_count_char_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → Nat.card {c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} * 2 ^ nfac P = 2 ^ (n * Fintype.card (InfinitePlace E)) := by
  first | exact @GlobalTheory.BCT.TwClassCount.main | exact GlobalTheory.BCT.TwClassCount.main | (intros; apply GlobalTheory.BCT.TwClassCount.main <;> assumption)
end

