import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0360
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0002

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOfEigen
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeckePointUniq
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem eq_of_eigen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i V hV x x' hx hx'
  classical
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hry : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (by rw [h, map_zero]))
  have hιinj : Function.Injective (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp
      (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) :=
    ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).injective.comp (Sp.iq i).injective).comp
      (IsFractionRing.injective (X.nd.O i) (FractionRing (X.nd.O i)))
  have key : ∀ v k, SplitOut X.nd i v → 1 ≤ k → k ≤ D.R.nV →
      (X.nd.hT i v k : X.nd.X i → X.nd.O i) x = (X.nd.hT i v k : X.nd.X i → X.nd.O i) x' := by
    intro v k hv hk1 hk2
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    have e1 := hx v k s ϖ hv hc hu hk1 hk2 y hyV
    have e2 := hx' v k s ϖ hv hc hu hk1 hk2 y hyV
    rw [e1] at e2
    exact hιinj (smul_left_injective ℂ hry e2)
  have hTle : X.nd.T i ≤ AlgHom.equalizer (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x)
      (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x') := by
    rw [← X.nd.T_gen i]
    refine Algebra.adjoin_le ?_
    rintro f ⟨v, k, h1, h2, h3, h4, hk1, hk2, rfl⟩
    exact key v k ⟨h1, h2, h3, h4⟩ hk1 hk2
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := X.nd.T_sep i x x' hne
  exact hfx (hTle hf)
end GlobalTheory.HeckePointUniq
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsRepOfTw
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.TwistAny
open Formalism.L2.NR
theorem exists_isRepOf_tw_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    rw [HChar.loc_mul, hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := rfl
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3
end GlobalTheory.HeightCounting.TwistAny
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsMuC
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.MuCLoc
theorem exists_muC_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  refine ⟨A.chr.e1.symm ⟨tp.tup (X.nd.mu i) j, tp.tup_unitary (X.nd.mu i) j⟩, ?_, ?_⟩
  · rw [A.chr.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ ((cf.isMu0 j).triv.mul (tp.xi_triv (X.nd.mu i)))
  · intro j' hj'
    have : j' = j := Fin.ext (by simp only [j]; omega)
    subst this
    rw [Equiv.apply_symm_apply]
end GlobalTheory.MuCLoc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsResidueFieldMap
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.ResidueLocPlace
end GlobalTheory.ResidueLocPlace
namespace GlobalTheory.ResidueLocPlace
end GlobalTheory.ResidueLocPlace
theorem GlobalTheory.ResidueLocPlace.exists_residueField_map_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  exact GlobalTheory.ResidueLocPlace.exists_residue_lift (X.nd.w_l i) _ _ (A.pl.ι (X.nd.w i)) (A.pl.plB (X.nd.w i))
    (A.pl.plB_eq (X.nd.w i)) (A.pl.plκ (X.nd.w i)) (Sp.iq i) (Sp.iq_alg i)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain
namespace GlobalTheory.CoefDuty
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}
def BuiltAlt (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)
def AutomorphicSideExists (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ big, ∃ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L
def ForcedByAutomorphicSemisimpleData (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (P : D7 → Prop) : Prop :=
  ∃ big, ∀ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → P (withLoc L)
end GlobalTheory.CoefDuty
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodPartLeISupEigen
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.FormsStep
theorem goodPart_le_iSup_eigen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b hj1 hj2
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b hj1 hj2
  have ha := descend_actL D T S In i j b hj1 hj2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  refine (GlobalTheory.T.V0T_le_span_image_goodL D S In T i j b hj1 hj2 (eIdem_all D) Φ hc ha he hw).trans (Submodule.span_le.mpr ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe]
  refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ (In.span j hj1 hj2 hx) ?_ ?_ ?_
  · intro σ y hy
    refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ hy ?_ ?_ ?_
    · intro hσ z hz
      refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ?_)
      rw [Submodule.mem_inf] at hz ⊢
      refine ⟨descend_mem_V0T D T S In i j b Φ hc ha he z hz.1, ?_⟩
      have hz2 := hz.2
      simp only [Submodule.mem_iInf] at hz2 ⊢
      intro k P hkP
      have hPb : P ∉ In.Sb := fun hP => hkP.2.2.2 (by
        rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
        exact Or.inr (Finset.mem_coe.mpr (hSb hP)))
      exact descend_mem_eigenspace D T S In i j b hj1 hj2 Φ hc hf k P _ z (hz2 k P ⟨hkP.1, hkP.2.1, hkP.2.2.1, hPb⟩)
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
  · rw [map_zero]; exact zero_mem _
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz
end GlobalTheory.HeightCounting.FormsStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.FitHecke
section NC
open Formalism.L2.NCov Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] {S : Set (End K V)}
end NC
section Conj
variable {R : Ranks}
end Conj
section Gen
variable {D : D7} {M : MtFam D}
end Gen
section Chars
open Formalism.L2.Host
end Chars
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heckeOpen_withLoc_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), ∃ Hk : _root_.GlobalTheory.HeightCounting.HeckeOpenStatements (withLoc L) (mtL L M) tp.tup, ∀ j h1 h2 π, Hk.au.cls j h1 h2 π = A.au.cls j h1 h2 π := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hjf : ∀ i : L.X.Loc, L.X.j i - 1 + 1 = L.X.j i := fun i => by have := L.X.j_range i; omega
  let jf : L.X.Loc → Fin D.R.m := fun i => ⟨L.X.j i - 1, by have := L.X.j_range i; omega⟩
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStd cover.B := Sp.std
  refine ⟨{ hecke := ?_, av := { S := Au.S, irr := Au.irr, inj := Au.inj, surj := Au.surj, typeV := Au.typeV, ptV := Au.ptV }, au := { A.au with }, emb := Au.emb, rational := rational_of cover, level := ?_, data := { bj := Sp.bj, bj_span := Sp.bj_span, bj_rel := fun i c => Sp.bj_rel i (sOf _ i) (sOf_spec _ i) c }, cover := cover }, fun j h1 h2 π => rfl⟩
  · refine { J_hyp := fun i => ?_
             hT := hT_of cover hstd Sp.act_hK
             sameO := sameO_of cover
             sep := sep_of cover hstd
             Q_conj := Q_conj_of cover
             Q_same := Q_same_of cover fun j j' w => (Sp.Qc_eq j w).trans (Sp.Qc_eq j' w).symm }
    have h0 := hMt.hyp (L.X.w i) (jf i)
    have h1 := hypOutside_transport' (M := M) (L.X.mu_w i).symm (hjf i) _ _ (L.X.j_range i).1 (L.X.j_range i).2 _ h0
    refine hypOutside_mono (D := withLoc L) _ _ ?_ h1
    have hi := mem_locs_self (D := withLoc L) i
    have hQe : C.Q (L.X.w i) = L.X.Q i := ((Sp.Q_eq _ _ i hi).trans (Sp.Qc_eq _ _)).symm
    intro v hv
    rcases hv with hv | hv
    · exact gPl_sub_badPl (D := withLoc L) i hv
    · obtain ⟨w', hov, hw'⟩ := qPl_sub tp (L.X.w i) (L.X.w_tw i) (jf i) hv
      refine ⟨w', hov, ?_⟩
      rcases hw' with hQ | hp
      · left
        rw [hQe] at hQ
        exact hQ
      · right; right
        rw [L.X.w_l i] at hp
        exact hp
  · refine { prod := ?_, para := ?_, uni := ?_, wt := ?_, hyp := ?_ }
    · exact fun i => mt_transport M (fun μ j m => NG.IsProdLevel m.J) (L.X.mu_w i).symm (hjf i) _ _ _ _
        (hMt.prod (L.X.w i) (jf i))
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ v ∈ qPl D (tp.tup μ j),
        ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelPara m.J m.χ s D.R.r ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.para (L.X.w i) j)
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E),
        s.w = D.naut.plGw k v → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.uni (L.X.w i) j)
    · intro μ j t sh a lam hinf hdual hhw
      have e := infG_etaT A.chr t
      have hsh : sh = 1 / 2 := by
        have := Multiset.singleton_inj.1 (hinf.symm.trans e)
        rw [this]; push_cast; ring
      rw [hsh]
      exact hMt.wt μ j t a lam hdual hhw
    · exact fun i j hj => mt_transport M (fun μ jj m => NG.HypOutside m.J m.χ (gPl D ∪ qPl D (tp.tup μ j)))
        (L.X.mu_w i).symm hj _ _ _ _ (hMt.hyp (L.X.w i) j)
end GlobalTheory.FitHecke
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAll
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.HeckeLat
local instance  (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) : Algebra (T.O i) (KT D T i b) :=
  inferInstanceAs (Algebra (T.O i) (FractionRing (T.O i)))
local instance  (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) : IsFractionRing (T.O i) (KT D T i b) :=
  inferInstanceAs (IsFractionRing (T.O i) (FractionRing (T.O i)))
end GlobalTheory.HeightCounting.HeckeLat
open GlobalTheory.HeightCounting.HeckeLat in
theorem GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P ⟨h1, h2, hk1, hk2, hsp, hP⟩ x hx
  obtain ⟨Φ, hc, hf, hw, hint, W0, hW0, hW0c, hrel⟩ := descend_integral D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  have hPb : P ∉ In.Sb := fun h => hP (by
    rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
    exact Or.inr (Finset.mem_coe.mpr (hSb h)))
  have hMW : ∀ y ∈ (S.A j).MK, y ∈ WKr D S j := fun y hy => by
    rw [WKr_of D S h1 h2]; exact hy.1
  have hML : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), Φ y ∈ BsupT D T S i j b := by
    have key : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), ∀ a : 𝓞 D.what₂.LL,
        Φ (a • y) ∈ BsupT D T S i j b := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro a
        obtain ⟨o, ho⟩ := hint a ⟨y, hMW y hy⟩
        rw [← algebraMap_smul D.what₂.LL a y]
        refine ho ▸ Submodule.smul_mem _ o ?_
        exact Submodule.subset_span ⟨⟨y, hMW y hy⟩, hy, hw _⟩
      | zero => intro a; rw [smul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => intro a; rw [smul_add, map_add]; exact add_mem (hy a) (hz a)
      | smul a' y _ hy => intro a; rw [smul_smul]; exact hy _
    intro y hy
    simpa using key y hy 1
  have hhr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    rw [dif_pos ⟨h1, h2⟩]
    rfl
  have hkΦ : ∀ y, hkT D T S In i j b k P (Φ y) = ((cHkT D T i b P : T.O i) ^ k) • Φ (In.hL j k P y) := by
    intro y
    rw [← algebraMap_smul (FractionRing (T.O i)), map_pow, hf _ _ hhr]
    rfl
  obtain ⟨n, hn⟩ := In.hL_int j k P h1 h2 hsp hPb hk2
  obtain ⟨u, hu⟩ := (normV_isUnit D T i P hP).pow n
  have hstep : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), y ∈ goodL D S In.θ j →
      hkT D T S In i j b k P (Φ y) ∈ BI D T S In i j b := by
    intro y hy hg
    rw [hkΦ]
    refine Submodule.smul_mem _ _ ⟨?_, ?_⟩
    · have h3 := hML _ (hn y hy hg)
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (T.O i), Nat.cast_pow, ← hu] at h3
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : T.O i) h3
      rwa [smul_smul, Units.inv_mul, one_smul] at h4
    · exact descend_mem_V0T D T S In i j b Φ hc ha he _ (hL_goodL D S In j k P h1 h2 ⟨hk1, hk2, hsp, hPb⟩ y hg)
  have hET : ∀ a y, Φ (eqL D S In.θ j a y) = eqT D T S In i j b a (Φ y) := by
    intro a y
    cases a with
    | none => simp only [eqL, eqT, LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
    | some u =>
      simp only [eqL, eqT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, ha, hc,
        LinearEquiv.coe_coe]
  have hx0 : ∀ a, eqT D T S In i j b a x = 0 := by
    intro a
    have h3 := goodTwistSideForms_le_span_goodLiftForms D S In T i j b h1 h2 (eIdem_all D) Φ hc ha he hw hx.2
    refine (Submodule.span_le (p := LinearMap.ker (eqT D T S In i j b a))).mpr ?_ h3
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hET, (mem_goodL_iff D S In.θ j y).mp hy a, map_zero]
  obtain ⟨m, o, g, rfl⟩ := Submodule.mem_span_set'.mp hx.1
  choose w hwM hwg using fun t => (g t).2
  have hg : ∀ t, (g t : FmT D T S i j b) = Φ (w t) := fun t => (hwg t).trans (hw _).symm
  simp only [hg] at hx0 ⊢
  haveI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hsol := hrel (fun t a => eqL D S In.θ j a (w t)) (fun t a => eqL_rational D S In j h1 h2 W0 hW0 hW0c a (w t)) o (by
    intro a
    rw [← hx0 a, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hET, LinearMap.map_smul_of_tower])
  clear hx0 hx
  induction hsol using Submodule.span_induction with
  | mem o ho =>
    obtain ⟨c, hc0, hco⟩ := ho
    have h3 : ∑ t, o t • Φ (w t) = Φ (∑ t, ((c t : ↥D.LL0) : D.what₂.LL) • (w t : S.WL j)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hc, ← hco, algebraMap_smul]
    rw [h3]
    refine hstep _ (Submodule.sum_mem _ fun t _ => ?_) ((mem_goodL_iff D S In.θ j _).mpr fun a => ?_)
    · let a : 𝓞 D.what₂.LL := ⟨((c t : ↥D.LL0) : D.what₂.LL),
        (RingOfIntegers.isIntegral_coe (c t)).map (algebraMap ↥D.LL0 D.what₂.LL).toIntAlgHom⟩
      have h4 := Submodule.smul_mem _ a (Submodule.subset_span (R := 𝓞 D.what₂.LL) (s := ((S.A j).MK : Set (S.WL j))) (hwM t))
      rwa [← algebraMap_smul D.what₂.LL a] at h4
    · rw [map_sum]
      simpa only [map_smul] using hc0 a
  | zero => simp
  | add o o' _ _ ho ho' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
    exact add_mem ho ho'
  | smul r o _ ho =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ ho
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtSplitOut
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.LocLevel
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem level_at_splitOut_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  intro D cf jE A M C tp hMI big X T Sp i w s hw hc κ htr
  classical
  have hov : NG.OverPl w s.v := overPl_of_isConjPl hc
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hS := (X.nd.S_def i w).not.1 hw.2.2.1
  have hl := hw.2.1
  have hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hp : w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl' hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hw.2.2.2 hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl' hov hov' hp')
  have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
    intro v hv
    apply htr v
    rintro rfl
    exact hv hvB
  exact hyp κ htr'
end GlobalTheory.LocLevel
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalLinkChar
section
set_option synthInstance.maxHeartbeats 200000

section
namespace Formalism.L2
def NGalTiedAlt.TupLink {D : Formalism.BasicNotions.D7} (G : _root_.Formalism.L2.NGalTiedAlt D) {C : Host.CharFrame D} {nch : Formalism.BasicNotions.NChoice D}
    (Tp : Host.TupTied D C nch) : Prop :=
  G.tup = Tp.tup
end Formalism.L2
end
end

