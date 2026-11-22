import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.MemLoc GlobalTheory.BKReal GlobalTheory.Prism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrisToDR

variable {l : ℕ} [Fact l.Prime]

def psiA (C : Core l) (K : FinExt l) : AK K →+* Per.BdRp l :=
  GlobalTheory.AinfK.lift (aDp l) (C.o.comp (K.1.val.toRingHom.comp (oK K))) fun w =>
    (GlobalTheory.SeedSec.o_eq_aDp_wA l (fK K) C w _
      (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) K w)).symm).symm

theorem psiA_inA (C : Core l) (K : FinExt l) (a : Ainf l) : psiA C K (inA K a) = aDp l a := lift_inA _ _ _ a

theorem psiA_inO (C : Core l) (K : FinExt l) (c : ↥(OL K)) :
    psiA C K (inO K c) = C.o ((oK K c : ↥K.1) : Om l) := lift_inO _ _ _ c

theorem thetaD_psiA (C : Core l) (K : FinExt l) (x : AK K) :
    Per.θD l (psiA C K x) = ((thetaK K x : OC l) : ℂ_[l]) :=
  GlobalTheory.AinfK.induction_on x (fun a c => by
    rw [map_mul, map_mul, map_mul, psiA_inA, psiA_inO, thetaK_inA, thetaK_inO, (thetaD_props l).2.2.2.1,
      C.o_sec.th]
    rfl)
    fun x y hx hy => by rw [map_add, map_add, map_add, hx, hy]; rfl

theorem mem_sq_of_psiA (C : Core l) (K : FinExt l) (x : AK K) (hx : thetaK K x = 0)
    (h2 : psiA C K x ∈ Per.FilP l 2) : x ∈ RingHom.ker (thetaK K) ^ 2 := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  have hk := ker_thetaK hπ hp
  obtain ⟨hF, hreg, -⟩ := filtration_eq_xi_pow l C.ε (core_isEps l C)
  have hdiv : ∀ y : AK K, thetaK K y = 0 → eta π p ∣ y := fun y hy => by
    rw [← Ideal.mem_span_singleton, ← hk]; exact hy
  obtain ⟨a, rfl⟩ := hdiv x hx
  have hξ : Per.θ l (xi C.ε) = 0 := by
    rw [← RingHom.mem_ker, C.ker_theta]; exact Ideal.mem_span_singleton_self _
  obtain ⟨b, hb⟩ := hdiv (inA K (xi C.ε)) (by rw [thetaK_inA, hξ])
  obtain ⟨z, hz⟩ := (hF 2 _).1 h2
  have hb' := congrArg (psiA C K) hb
  rw [psiA_inA, map_mul] at hb'
  rw [map_mul] at hz
  have h3 : psiA C K a - aDp l (xi C.ε) * (z * psiA C K b) = 0 := hreg _ (by
    linear_combination psiA C K a * hb' + psiA C K b * hz)
  have h4 := congrArg (Per.θD l) h3
  rw [map_sub, map_mul, (thetaD_props l).2.2.2.1, hξ, thetaD_psiA, map_zero] at h4
  have h5 : thetaK K a = 0 := Subtype.ext (by simpa using h4)
  rw [pow_two]
  exact Ideal.mul_mem_mul (thetaK_eta hp) h5

private theorem aB_eq_aC_pt (a : Ainf l) :
    Per.aB l a = algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) := GlobalTheory.RingIface.aB_eq_alg l a

private theorem j_aC_pt (C : Core l) (a : Ainf l) : C.j (aC l a) = aDp l a :=
  (congrArg C.j (GlobalTheory.RingIface.tower l a)).trans
    (C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) a))

theorem exists_map : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ K : FinExt l, ∃ Ψ : BK K →+* P.R.BdR,
      (∀ c : ↥K.1, Ψ (inK K c) = algebraMap ↥K.1 P.R.BdR c) ∧
      (∀ (g : ↥(GK K)) (b : BK K), (P.PD K).actdR g (Ψ b) = Ψ (galB g b)) ∧
      (∀ b, Ψ b ∈ (P.PD K).Fil 0) ∧
      (∀ x : AK K, thetaK K x = 0 → Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil 1) ∧
      (∀ x : AK K, thetaK K x = 0 → x ∉ RingHom.ker (thetaK K) ^ 2 → Ψ (toB K (ofA K x)) ∉ (P.PD K).Fil 2) := by
  intro l _ P AI ⟨T⟩ K
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  let j : Per.Acris l →+* P.R.B := T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))
  let u : Per.Acris l →+* P.R.BdR := (P.PD K).ι.toRingHom.comp j
  have hu : ∀ a, u a = (P.PD K).ι (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) := fun _ => rfl
  have huv : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = algebraMap ↥K.1 P.R.BdR (oK K (thetaW (fK K) K w)) := fun w =>
    (GlobalTheory.WittCompat.exists_unramified_witt_element l P AI T K w).elim fun c hc =>
      (((congrArg (fun b => (P.PD K).ι (T.eB.symm b)) (aB_eq_aC_pt _).symm).trans
        (congrArg (P.PD K).ι hc.2).symm).trans ((P.PD K).ι.commutes c)).trans
        ((IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR c).trans (congrArg _ hc.1))
  have h1 := liftB_inK u (algebraMap ↥K.1 P.R.BdR) huv
  have h2 := liftB_inC u (algebraMap ↥K.1 P.R.BdR) huv
  generalize liftB u (algebraMap ↥K.1 P.R.BdR) huv = Ψ at h1 h2
  have hD : ∀ a, T.eD (u a) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j a) := fun a => by
    rw [hu, P.PD_ι, hC.ι, RingEquiv.apply_symm_apply, C.ι_j]
  have hA : ∀ x : AK K, T.eD (Ψ (toB K (ofA K x))) = algebraMap (Per.BdRp l) (Per.BdR l) (psiA C K x) := fun x =>
    GlobalTheory.AinfK.induction_on x (fun a c => by
      simp only [map_mul]
      rw [ofA_inA, ofA_inO, ← inK_oK, h1, h2, hD, psiA_inA, psiA_inO]
      congr 1
      · exact congrArg _ (j_aC_pt C a)
      · exact hC.o _)
      fun x y hx hy => by simp only [map_add, hx, hy]
  have hfil : ∀ (n : ℕ) (x : AK K), Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil n ↔ psiA C K x ∈ Per.FilP l n := fun n x => by
    rw [T.fil, hA, GlobalTheory.BKGal.TaylorFil.alg_mem_FilD_iff]
  have hsm : ∀ (c : ↥K.1) (b : BK K), Ψ (inK K c * b) = c • Ψ b := fun c b => by
    rw [map_mul, h1, Algebra.smul_def]
  refine ⟨Ψ, h1, fun g b => ?_, fun b => ?_, fun x hx => ?_, fun x hx hx2 h => ?_⟩
  · refine RingHom.congr_fun (GlobalTheory.PZ.ColmezVec.ext_BK (((P.PD K).actdR g).toAlgHom.toRingHom.comp Ψ)
      (Ψ.comp (galB g)) (fun c => ?_) fun a => ?_) b
    · rw [RingHom.comp_apply, RingHom.comp_apply, galB_inK, h1]
      exact ((P.PD K).actdR g).commutes c
    · rw [RingHom.comp_apply, RingHom.comp_apply, galB_toB, galC_inC, h2, h2, hu, hu,
        ← GlobalTheory.PZ.ColmezVec.act_acris T K g, (P.PD K).ι_comm]
      rfl
  · obtain ⟨D, z, hz⟩ := exists_pow_mul b
    have hz0 : Ψ (toB K z) ∈ (P.PD K).Fil 0 := GlobalTheory.AcrisK.induction_on z (fun a c => by
      rw [map_mul, ← inK_oK, mul_comm, hsm, h2]
      refine Submodule.smul_mem _ _ ?_
      rw [T.fil, hD]
      exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _)
      fun x y hx hy => by rw [map_add, map_add]; exact add_mem hx hy
    have hl : ((l : ↥K.1) ^ D) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    rw [← hz, ← map_natCast (inK K), ← map_pow, hsm] at hz0
    exact (Submodule.smul_mem_iff _ hl).1 hz0
  · refine (hfil 1 x).2 (((thetaD_props l).2.1 _).1 ?_)
    rw [thetaD_psiA, hx]
    rfl
  · exact hx2 (mem_sq_of_psiA C K x hx ((hfil 2 x).1 h))

end GlobalTheory.CrisToDR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyDerivCompNeg
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Parity

theorem polyDeriv_comp_neg {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (P : MvPolynomial σ ℂ) (d : ℕ)
    (hP : P.IsHomogeneous d) (u : σ → W) (F : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => F (-z)) 0 = (-1) ^ d * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    rw [Finsupp.card_toMultiset, ← hP (MvPolynomial.mem_support_iff.1 hm), Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have h := (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W).iteratedFDerivWithin_comp_right F uniqueDiffOn_univ
    (x := 0) (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have e : (fun z => F (-z)) = F ∘ (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  have e2 : ∀ t : W, ((ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) : W →L[ℂ] W) t = (-1 : ℂ) • t := fun t => by simp
  simp only [e2]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hd]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

def reflTF (n g : ℕ) : TF n g ≃+ TF n g where
  toFun φ := fun x => φ (-x)
  invFun φ := fun x => φ (-x)
  left_inv φ := by funext x; simp
  right_inv φ := by funext x; simp
  map_add' _ _ := rfl

theorem reflTF_smul (a : ℂ) (φ : TF n g) : reflTF n g (a • φ) = a • reflTF n g φ := rfl

theorem isSB_reflTF {φ : TF n g} (h : GlobalTheory.SW.IsSB φ) : GlobalTheory.SW.IsSB (reflTF n g φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h1 (-x) hx k i).neg
    simpa using this
  · have := h2 (-x) (-y) fun k i => (hy k i).neg
    change φ _ = φ _
    rw [← this, neg_add, smul_neg]

theorem thA_reflTF (φ : TF n g) (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (reflTF n g φ) x z = thA X bas idx φ x (-z) := by
  unfold thA thS
  congr 1
  · simp only [Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  · rw [← (Equiv.neg (Matrix (Fin n) (Fin g) ℚ)).tsum_eq]
    refine tsum_congr fun y => ?_
    have e : ∀ k, qv ((-y) k) = -qv (y k) := fun k => by
      funext i
      simp [qv]
    have e' : reflTF n g φ (-y) = φ y := by
      change φ (- -y) = φ y
      rw [neg_neg]
    simp only [Equiv.neg_apply, e, e', Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem reflTF_heisG (hs : IsSympl X bas) (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) :
    reflTF n g (heisG X bas y φ) = heisG X bas (-y) (reflTF n g φ) := by
  have e : ∀ k, crd X bas ((-y) k) = -crd X bas (y k) := fun k => by
    have := crd_smul hs (-1) (y k)
    rw [neg_one_smul, neg_one_smul] at this
    exact this
  funext x
  change heisS _ _ φ (-x) = φ _ * _
  unfold heisS
  congr 2
  · ext k i
    simp [e]
    ring
  · congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [e, dotProduct]

theorem EF_neg_smul_neg (w : E) (u : Fin r → E) : EF X (-u) (w • -u) = EF X u (w • u) := by
  change EFBil X _ _ = EFBil X _ _
  simp

theorem epsW_neg (w : E) (y : Matrix (Fin n) (Fin r) E) : epsW X w (-y) = epsW X w y := by
  have e : ∀ k, (-y) k = -(y k) := fun _ => rfl
  simp only [epsW, e, EF_neg_smul_neg]

theorem reflTF_projA (hs : IsSympl X bas) (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) {φ : TF n g}
    (hφ : reflTF n g φ = φ) : reflTF n g (projA X bas w A φ) = projA X bas w A φ := by
  unfold projA
  rw [reflTF_smul]
  congr 1
  have hm : Set.MapsTo (reflTF n g) ((fun y => epsW X w y • heisG X bas y φ) '' A)
      ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, A.neg_mem hy, by simp only [reflTF_smul, reflTF_heisG hs, hφ, epsW_neg]⟩
  have hi : ∀ ψ, reflTF n g (reflTF n g ψ) = ψ := (reflTF n g).left_inv
  rw [AddEquiv.map_finsum]
  simp only [AddEquiv.map_finsum]
  exact finsum_mem_eq_of_bijOn (reflTF n g)
    ⟨hm, (reflTF n g).injective.injOn, fun ψ hψ => ⟨_, hm hψ, hi ψ⟩⟩ fun _ _ => rfl

theorem isTheta1_neg {w : E} {x : Frame X.Ψ r} {L : Lt E r} {θ : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L θ) : IsTheta1 X bas idx w x L fun z => θ (-z) := by
  refine ⟨h.1.comp differentiable_id.neg, fun v hv => ?_⟩
  funext z
  have := congrFun (h.2 (-v) (L.neg_mem hv)) (-z)
  have e : pv X idx x (-v) = -pv X idx x v := by
    unfold pv
    rw [per_neg]
    rfl
  simp only [Pi.smul_apply, fock, eps1, EF_neg_smul_neg, e] at this ⊢
  rw [← this, smul_neg, ← neg_add, ← neg_add]
  simp only [hx, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem isTheta1_update (hs : IsSympl X bas) (hn : Even n) {w : E} {L : Lt E r} {v : TF n g}
    (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) (z₀ : Fin n → Fin g → ℂ) (b : Fin n) :
    IsTheta1 X bas idx w x L fun t => thA X bas idx v x (Function.update z₀ b t) := by
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1
  refine ⟨h2.comp (differentiable_pi.2 fun k => ?_), fun u hu => ?_⟩
  · by_cases hk : k = b
    · subst hk
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne hk]
      exact differentiable_const _
  · funext t
    set y : Matrix (Fin n) (Fin r) E := Pi.single b u with hy
    have hyb : y b = u := Pi.single_eq_same _ _
    have hyk : ∀ k, k ≠ b → y k = 0 := fun k hk => Pi.single_eq_of_ne hk _
    have hm : y ∈ tens (stdL E n) L := (TensLat.mem_tens_stdL L _).2 fun k => by
      by_cases hk : k = b
      · rw [hk, hyb]; exact hu
      · rw [hyk k hk]; exact L.zero_mem
    have hp : pv X idx x 0 = 0 := by
      unfold pv
      rw [per_zero]
      rfl
    have e1 : epsW X w y = eps1 X w u := by
      unfold epsW eps1
      rw [Finset.sum_eq_single b, hyb]
      · intro k _ hk
        rw [hyk k hk]
        change EFBil X _ _ = 0
        simp
      · simp
    have e2 := (h1 y (Function.update z₀ b t)).2
    rw [Finset.sum_eq_single b, hyb, Function.update_self] at e2
    · have e3 : (fun k => Function.update z₀ b t k + pv X idx x (y k)) = Function.update z₀ b (t + pv X idx x u) := by
        funext k
        by_cases hk : k = b
        · rw [hk, hyb, Function.update_self, Function.update_self]
        · rw [hyk k hk, hp, add_zero, Function.update_of_ne hk, Function.update_of_ne hk]
      rw [e3] at e2
      conv_rhs => rw [← hv.2.2 y hm, GlobalTheory.SW.UnAct.thA_smul]
      simp only [Pi.smul_apply, fock, e1, e2, Nat.cast_one, _root_.one_mul]
    · intro k _ hk
      rw [hyk k hk, hp]
      simp [hx]
    · simp

include idx in

theorem reflTF_vac (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r}
    (hL : SelfD X L) {v : TF n g} (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) :
    reflTF n g v = v := by
  refine (((thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1).2.2 _ (isSB_reflTF hv.1)).2 ?_).symm
  funext z
  rw [thA_reflTF]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Subsingleton.elim (-z) z]
  by_cases h0 : thA X bas idx v x = 0
  · simp [h0]
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  have hθ := isTheta1_update idx hs hn hv hd z₀ ⟨0, hpos⟩
  set θ := fun t => thA X bas idx v x (Function.update z₀ ⟨0, hpos⟩ t) with hθd
  have ht : θ (z₀ ⟨0, hpos⟩) ≠ 0 := by simpa [hθd] using hz₀
  obtain ⟨a, ha⟩ := GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx n hs hn w hw hw' L hL x hd _ θ
    (isTheta1_neg idx hθ) hθ (Function.ne_iff.2 ⟨_, ht⟩)
  have ha' : ∀ t, θ (-t) = a * θ t := congrFun ha
  have haa : a ^ 2 = 1 := by
    have := ha' (-z₀ ⟨0, hpos⟩)
    rw [neg_neg, ha'] at this
    exact mul_right_cancel₀ ht (by linear_combination -this)
  obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g bas idx n hs hn w hw hw' L hL v hv x hd θ hθ
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have := hκ fun _ => z₀ ⟨0, hpos⟩
    rw [zero_mul] at this
    exact Finset.prod_ne_zero_iff.2 (fun _ _ => ht) this
  refine mul_left_cancel₀ hκ0 ?_
  rw [← hκ, ← hκ]
  obtain ⟨m, hm⟩ := hn
  have : a ^ n = 1 := by rw [hm, ← two_mul, pow_mul, haa, one_pow]
  simp only [Pi.neg_apply, ha', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, this,
    _root_.one_mul]

theorem thP_gphi_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ Λ : Formalism.L2.Pj.GenLat E n, Λ.Unimod → Λ.La.FG → ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ∀ x ∈ X.dom, thP X hq bas idx (gphi X bas w Λ.La L v c (fun q => -Y q)) P x = (-1) ^ d * thP X hq bas idx (gphi X bas w Λ.La L v c Y) P x := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq w hw hw' L hL v hv Λ _ _ Q _ c Y P d hP x hd
  have h1 := reflTF_projA hs w (tens Λ.La L) (reflTF_vac idx hs hn hw hw' hL hv hd)
  have h2 : gphi X bas w Λ.La L v c (fun q => -Y q) = reflTF n g (gphi X bas w Λ.La L v c Y) := by
    unfold gphi
    rw [AddEquiv.map_finsum]
    simp only [reflTF_smul, reflTF_heisG hs, h1]
  unfold thP
  rw [h2, ← polyDeriv_comp_neg P d hP]
  congr 1
  funext z
  exact thA_reflTF idx _ x z

end GlobalTheory.AdTh.Parity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProof
section
open GlobalTheory.IsoTriv

namespace GlobalTheory.IsoTriv.PrimeIdempotent

theorem mem_pow_of_map_dvd {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V) (b a : R) (hb : φ b ≠ 0) (n : ℕ)
    (hw : (Ideal.comap φ (IsLocalRing.maximalIdeal V)).IsMaximal)
    (hbn : b ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n) (z : V) (hz : φ a = φ b * z) :
    a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n := by
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  by_cases ha : a = 0
  · rw [ha]; exact Ideal.zero_mem _
  have hspan : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i
    at hfac
  by_cases hi : n ≤ i
  · have h1 : a ∈ w ^ i * J := hfac ▸ Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1
  exfalso
  have hJw : ¬ J ≤ w := fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])
  obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.mp hJw
  have hb1 : b ∈ w ^ (i + 1) := Ideal.pow_le_pow_right (by omega) hbn
  have h2 : b * s ∈ Ideal.span {a} * w := by
    rw [hfac, mul_right_comm, ← pow_succ]
    exact Ideal.mul_mem_mul hb1 hsJ
  obtain ⟨m, hm, hm'⟩ := Ideal.mem_span_singleton_mul.mp h2
  apply hsw
  have h3 : φ s = z * φ m := by
    apply mul_left_cancel₀ hb
    rw [← map_mul, ← hm', map_mul, hz, mul_assoc]
  change φ s ∈ IsLocalRing.maximalIdeal V
  rw [h3]
  exact Ideal.mul_mem_left _ _ hm

theorem epsSt : EpsSt := by
  intro R V _ _ _ _ _ φ q hq hu
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  have hqw : q ∈ w := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hw0 : w ≠ ⊥ := fun h => hq0 (by rw [h] at hqw; exact hqw)
  have hw : w.IsMaximal := hwp.isMaximal hw0
  have hspan : Ideal.span {q} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e
    at hfac
  have hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M := fun M => by
    rw [← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z := by
    intro N
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ
    have hco : w ^ k ⊔ J ^ N = ⊤ := Ideal.pow_sup_pow_eq_top hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)
    have h1 : φ x ∈ Ideal.span {φ q ^ N} := by
      have h2 : φ x ∈ (Ideal.map φ w) ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx
      have h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k :=
        Ideal.pow_right_mono Ideal.map_comap_le k h2
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h3
      rwa [Ideal.span_singleton_eq_span_singleton.mpr hk]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    refine ⟨y, hy, -c, ?_⟩
    have h4 : φ x + φ y = 1 := by rw [← map_add, hxy, map_one]
    rw [← h4, hc]; ring
  choose ε hεJ hε using key
  refine ⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩
  have hqM : q ^ M ∈ w ^ (e * M) := by
    have h1 : q ^ M ∈ w ^ (e * M) * J ^ M := hpow M ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf h1).1
  have ha : a ∈ w ^ (e * M) :=
    mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z
      (by rw [map_pow]; exact hz)
  rw [hpow M, mul_comm (ε N)]
  exact Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))

end GlobalTheory.IsoTriv.PrimeIdempotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGenericStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properGroupScheme_dvr_sections_mulEquiv_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  first | exact @GlobalTheory.LevExt.sections_generic_mulEquiv | exact GlobalTheory.LevExt.sections_generic_mulEquiv | (intros; apply GlobalTheory.LevExt.sections_generic_mulEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiHalfSymplecticOrthonormalFrameStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_halfSymplectic_orthonormalFrame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr | exact GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr | (intros; apply GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogenyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ Q₁ Q₂ : LB (G2 A').left, Q₁.IsLB → Q₂.IsLB → (∃ t : (Q₁.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₁.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Q₁.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) (Q₂.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  first | exact @GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt | exact GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt | (intros; apply GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiReflectionPairTruncationMemClosureStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiReflectionPair_truncation_mem_closure : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.SUPair.trunc_pair_mem | exact GlobalTheory.SUPair.trunc_pair_mem | (intros; apply GlobalTheory.SUPair.trunc_pair_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIffStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff : ∀ (D : D7) (V : HSp D) (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ a : Fin V.rank → D.host.E, finVec V a ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} ↔ a ∈ I • latG V 1 := by
  first | exact @GlobalTheory.IdealCap.finVec_mem_closure_iff | exact GlobalTheory.IdealCap.finVec_mem_closure_iff | (intros; apply GlobalTheory.IdealCap.finVec_mem_closure_iff <;> assumption)
end

