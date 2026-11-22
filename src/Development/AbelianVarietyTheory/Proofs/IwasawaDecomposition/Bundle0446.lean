import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionProperties
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtRed

section Split

open ReciprocityTheory.Aut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)

theorem i_mem (a : 𝓞 E) : s.i (a : E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (s.split_le_one a)

def iInt : 𝓞 E →+* s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  ((s.i : E →+* s.v.adicCompletion (maximalRealSubfield E)).comp (algebraMap (𝓞 E) E)).codRestrict _ (i_mem s)

theorem mem_max_iff (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    x ∈ IsLocalRing.maximalIdeal (s.v.adicCompletionIntegers (maximalRealSubfield E)) ↔
      Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

def psiR : 𝓞 E →+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  (IsLocalRing.residue _).comp (iInt s)

theorem psiR_eq_zero (a : 𝓞 E) : psiR s a = 0 ↔ a ∈ s.w.asIdeal := by
  rw [psiR, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  exact Iff.rfl

theorem psiR_surj : Function.Surjective (psiR s) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  obtain ⟨a, ha⟩ := adic_exists_approx s.v _ hx
  refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a, ?_⟩
  rw [psiR, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((iInt s (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
      s.v.adicCompletion (maximalRealSubfield E)) = algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) a := by
    show s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a : 𝓞 E)) : E) = _
    rw [split_coe_algebraMap, AlgHom.commutes]; rfl
  rw [AddSubgroupClass.coe_sub, e, Valuation.map_sub_swap]
  exact ha

def kEqv : kP s.w ≃+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  RingEquiv.ofBijective (Ideal.Quotient.lift s.w.asIdeal (psiR s) fun a ha => (psiR_eq_zero s a).2 ha)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [Ideal.Quotient.lift_mk, psiR_eq_zero] at hq
      exact Ideal.Quotient.eq_zero_iff_mem.2 hq,
    fun y => by
      obtain ⟨a, rfl⟩ := psiR_surj s y
      exact ⟨Ideal.Quotient.mk s.w.asIdeal a, Ideal.Quotient.lift_mk _ _ _⟩⟩

def phiR : s.v.adicCompletionIntegers (maximalRealSubfield E) →+* kP s.w :=
  ((kEqv s).symm : _ →+* kP s.w).comp (IsLocalRing.residue _)

theorem phiR_surj : Function.Surjective (phiR s) :=
  (kEqv s).symm.surjective.comp IsLocalRing.residue_surjective

theorem phiR_eq_zero (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    phiR s x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (kEqv s).symm.injective,
    IsLocalRing.residue_eq_zero_iff, mem_max_iff]

theorem kEqv_mk (a : 𝓞 E) : kEqv s (Ideal.Quotient.mk s.w.asIdeal a) = psiR s a :=
  Ideal.Quotient.lift_mk s.w.asIdeal (psiR s) (fun a ha => (psiR_eq_zero s a).2 ha)

theorem phiR_i (a : 𝓞 E) : phiR s ⟨_, i_mem s a⟩ = Ideal.Quotient.mk s.w.asIdeal a := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  rw [kEqv_mk]; rfl

theorem exists_approx (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    ∃ a : 𝓞 E, Valued.v ((x : s.v.adicCompletion (maximalRealSubfield E)) - s.i (a : E)) < 1 ∧
      phiR s x = Ideal.Quotient.mk s.w.asIdeal a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (phiR s x)
  refine ⟨a, ?_, ha.symm⟩
  have h : phiR s (x - ⟨_, i_mem s a⟩) = 0 := by
    rw [map_sub, phiR_i, ha, sub_self]
  have h2 := (phiR_eq_zero s _).1 h
  rwa [AddSubgroupClass.coe_sub] at h2

end Split

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem km_mem_UA (κ : Formalism.AUTREP.GAf D.host.E n) : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
  show Formalism.UG.cT (GlobalTheory.StdFrameExist.sgA D) (GlobalTheory.StdFrameExist.kmat κ).1 *
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *
      (GlobalTheory.StdFrameExist.kmat κ).1 = (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, GlobalTheory.StdFrameExist.cT_kmat]

theorem km_mem_St_iff (κ : Formalism.AUTREP.GAf D.host.E n) :
    km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  rw [GlobalTheory.StdFrameExist.mem_Umax_iff]
  constructor
  · rintro ⟨y, hy⟩ i j
    have e : (GlobalTheory.StdFrameExist.kmat κ).1 i j = ((y.1 i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      show (km D n κ).1 i j = _
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    rw [e]
    exact (y.1 i j).2
  · intro h
    have h' : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 :=
      (GlobalTheory.StdFrameExist.mem_Umax_iff _).1 (inv_mem ((GlobalTheory.StdFrameExist.mem_Umax_iff κ).2 h))
    have hm : (GlobalTheory.StdFrameExist.kmat κ).1 * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.mul_inv]
    have hm' : (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 * (GlobalTheory.StdFrameExist.kmat κ).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.inv_mul]
    refine ⟨⟨Matrix.of fun i j => ⟨_, h i j⟩, Matrix.of fun i j => ⟨_, h' i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have := congrFun (congrFun hm i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ).1 i x * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · ext i j
      have := congrFun (congrFun hm' i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 i x * (GlobalTheory.StdFrameExist.kmat κ).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · apply Units.ext
      ext i j
      simp [frGL, intGL, Formalism.UG.bc]
      rfl

theorem red_eq_one (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (PP : Pl D.host.E) (hT : ReciprocityTheory.Aut.TrivOutside A κ) (hP : NG.OverPl PP v) (hv : v ∉ A) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  refine Formalism.L2.DIV.reduction_local D.host.F D.host.E n 1 PP v hP.symm _ ((km_mem_St_iff D n κ).2 hκ) ?_
  have h := hT v hv
  apply Units.ext
  ext i j
  have e := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at e
  exact e

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem red_split (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a b : Fin n) :
    ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = phiR s ⟨_, h⟩ := by
  obtain ⟨y, hy⟩ := (km_mem_St_iff D n κ).2 hκ
  have hz : (κ.1.val a b) ∈ ReciprocityTheory.Aut.ALint D.host.E := hκ a b
  have hz' := GlobalTheory.RowGood.tr_int rfl hz
  rw [GlobalTheory.RowGood.tr_rfl] at hz'
  have hmem : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s hz')
  refine ⟨hmem, ?_⟩
  obtain ⟨c, hc, hφ⟩ := exists_approx s ⟨_, hmem⟩
  rw [hφ]
  have hyab : ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = κ.1.val a b := by
    have e : (km D n κ).1 a b = ((y.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    exact e.symm
  rw [← hy, redFn_frGL]
  have := GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (κ.1.val a b) (y.val a b)
    (by rw [GlobalTheory.RowGood.tr_rfl]; exact hyab) c hc
  exact this

end GlobalTheory.MtRed

end

namespace GlobalTheory.MtRed

theorem km_reduction : ∀ (D : D7) (n : ℕ), (∀ κ, km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E)) ∧ (∀ κ, km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n) ∧ (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v) (PP : Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w, Function.Surjective φ ∧ (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) ∧ (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) ∧ ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ a b, ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = φ ⟨_, h⟩ := by
  intro D n
  exact ⟨km_mem_UA D n, km_mem_St_iff D n, fun κ hκ A v PP hT hP hv => red_eq_one D n κ hκ A v PP hT hP hv,
    fun s => ⟨phiR s, phiR_surj s, phiR_eq_zero s, fun a => ⟨i_mem s a, phiR_i s a⟩,
      fun κ hκ a b => red_split D n κ hκ s a b⟩⟩

end GlobalTheory.MtRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKOfStd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.KerSK

theorem rowSG_heq {ι : Type} {X X' : Fields} (hX : X = X') {Pr : Primes X} {Pr' : Primes X'} (hPr : HEq Pr Pr')
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    (hsel : HEq sel sel') {S S' : Set ℕ} (hS : S = S') {tup : ι → Tup X.F X.E X.K S} {tup' : ι → Tup X'.F X'.E X'.K S'}
    (htup : HEq tup tup') :
    HEq (fun μ => rowSG Pr sel (tup μ)) (fun μ => rowSG Pr' sel' (tup' μ)) := by
  subst hX; subst hS; cases hPr; cases hsel; cases htup; rfl

theorem sharp_heq {ι : Type} {X X' : Fields} (hX : X = X') {P : ι → Finset (HeightOneSpectrum (𝓞 X.E))}
    {P' : ι → Finset (HeightOneSpectrum (𝓞 X'.E))} (hP : HEq P P') {c : ∀ μ, LocCst X (P μ)} {c' : ∀ μ, LocCst X' (P' μ)}
    (h : HEq c c') (μ : ι) : (c μ).sharp = (c' μ).sharp := by
  subst hX; cases hP; cases h; rfl

theorem ch_cast {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
    {Tw Tw' : TwForms D} (h : Tw = Tw') (x : SymmetricTwistedColumnsAtPrimes tp C Tw) : (h ▸ x).ch = x.ch := by
  subst h; rfl

end GlobalTheory.Mem.Col2.TC.KerSK

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.tiedSK_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : Formalism.L2.LinkedFamilyData ex) (he : ex.tw = I.tw l l0 Z) (t : KerEntTied ex), I.StdC l Z T.cols → I.StdTw l Z l0 (he ▸ T.tw) → I.StdKer l Z t → ∃ S : Formalism.L2.TiedDataSK ex, S.toTiedDataS = T ∧ S.ker = t := by
  intro B X I hI hP l Z l0 L hT Gi Gl K Y cX ex T he t hC hTw hK
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  refine ⟨{ T with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [KerSK.sharp_heq hK.X_eq (KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact hI.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Units.val (1 : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpKeepsChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section SameUp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem SameG.up' {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (q : 𝓞 X.E) {x : Sp X.E n}
    (hx : x ∈ p.1.1.deco.1.N) : SameG p (p.mv (p.1.1.deco.up P q x)) := by
  classical
  have hs : DecoSet.SameOn SG p.1.1.deco (p.1.1.deco.up P q x) :=
    DecoSet.sameOn_up _ P hP.ne (fun w hw => hP.sg ⟨w, hw⟩) q hx
  have hb : (p.1.1.deco.up P q x).1.be = p.1.1.deco.1.be := by
    unfold DecoSet.up
    split_ifs with h
    · rfl
    · rfl
  by_cases h : (∀ (w : Q) (z : Sp X.E n), p.1.1.1.2 w z ∈ (p.1.1.deco.up P q x).1.at w.1 ↔ z ∈ stdAt X.E n w.1) ∧ p.1.2 ∈ y.ys (p.1.1.deco.up P q x).1.N
  · have e : p.mv (p.1.1.deco.up P q x) = ⟨(⟨(p.1.1.deco.up P q x, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    exact ⟨rfl, rfl, fun w => hs w.1 w.2, hb⟩
  · have e : p.mv (p.1.1.deco.up P q x) = p := dif_neg h
    rw [e]
    exact SameG.refl p

end SameUp

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.cosetIn_rep_up (hX : B.fields.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (x : ((I.atIn u a).A i).lv v c) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).upPt v c x))) =
      cosetIn ((I.stp u a i).rep c) := by
  by_cases hj : i + 1 = B.R.m
  · refine GStep.prefRep_eq_of_normal (I.stp0 u a i) c.1 (fun q' : (I.stp0 u a i).D c.1 => cosetIn q') (I.pref u a i c.1)
      (GStep.prefRep_normal (I.stp0 u a i) c.1 _ _ (fun p hp => hp.2.1 hj) (I.pref_of_normalFor u a i hj c.1)) c.2 _ fun h => ?_
    exact cosetIn_eq_of_sameG hX hPr (SameG.smul h (SameG.up' ((I.stp u a i).rep c) v (moveHyp_of_ok hPr u v) _
      (Quotient.out x).2))
  · have h0 : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn q = fun _ => ∅ := by
      intro q
      funext P
      have hq : q.1.2 = ∅ := by
        have := q.2
        rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
        exact this
      ext z
      simp [cosetIn, hq]
    rw [h0, h0]

end GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem TC.up_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K → ∀ (v : (I.atT l u a).vT) (c : (I.chain l u a).cls i) (x : (I.fm l u a).lv i v c), (I.fm l u a).fv i v c x = 1 → chOf ((I.fm l u a).up i v c x) = chOf c := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K hR v c x _
  obtain ⟨k, hk⟩ := hR
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  exact (hk.key ((I.fm l u a).up i v c x) c).2 ⟨rfl, I.cosetIn_rep_up hX l.pr u a i v c x⟩

end GlobalTheory.Mem.Col2
end

