import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0041
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactUnitaryOfSplitPlaceLift
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LiftInt

section Val

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

def ltIdeal : Ideal v.integer where
  carrier := {x | v (x : K) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul] at *
    calc v (c : K) * v (x : K) ≤ 1 * v (x : K) := by gcongr; exact c.2
      _ < 1 := by rwa [one_mul]

theorem det_sub_lt {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1)
    (hB : ∀ i j, v (B i j) ≤ 1) (h : ∀ i j, v (A i j - B i j) < 1) : v (A.det - B.det) < 1 := by
  let A0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨B i j, hB i j⟩
  have eA : A0.map v.integer.subtype = A := by ext i j; rfl
  have eB : B0.map v.integer.subtype = B := by ext i j; rfl
  have hm : A0.map (Ideal.Quotient.mk (ltIdeal v)) = B0.map (Ideal.Quotient.mk (ltIdeal v)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact h i j
  have hd := congrArg Matrix.det hm
  have d1 : Ideal.Quotient.mk (ltIdeal v) A0.det = (A0.map (Ideal.Quotient.mk (ltIdeal v))).det :=
    RingHom.map_det _ _
  have d2 : Ideal.Quotient.mk (ltIdeal v) B0.det = (B0.map (Ideal.Quotient.mk (ltIdeal v))).det :=
    RingHom.map_det _ _
  rw [← d1, ← d2, Ideal.Quotient.eq] at hd
  have e1 : v.integer.subtype A0.det = (A0.map v.integer.subtype).det := RingHom.map_det _ _
  have e2 : v.integer.subtype B0.det = (B0.map v.integer.subtype).det := RingHom.map_det _ _
  rw [eA] at e1
  rw [eB] at e2
  have : v ((A0.det - B0.det : v.integer) : K) < 1 := hd
  rw [← e1, ← e2, ← map_sub]
  exact this

theorem adjugate_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    ∀ i j, v (A.adjugate i j) ≤ 1 := by
  let A0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have eA : A0.map v.integer.subtype = A := by ext i j; rfl
  have e : A0.adjugate.map v.integer.subtype = (A0.map v.integer.subtype).adjugate :=
    RingHom.map_adjugate _ _
  rw [eA] at e
  intro i j
  rw [← e]
  exact (A0.adjugate i j).2

end Val

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intCast_le_one (s : SplitPlace L) (m : ℤ) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) ≤ 1 := by
  have h := s.split_le_one (m : 𝓞 L)
  simpa using h

theorem natCast_lt_one (s : SplitPlace L) (g : ℕ) (hg : ((g : 𝓞 L) ∈ s.w.asIdeal)) :
    Valued.v ((g : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
  have h : Valued.v (s.i ((g : 𝓞 L) : L)) < 1 := hg
  simpa using h

theorem intCast_eq_one (s : SplitPlace L) (g : ℕ) (hp : g.Prime) (hg : ((g : 𝓞 L) ∈ s.w.asIdeal)) (m : ℤ)
    (hm : ¬ (g : ℤ) ∣ m) : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  have hcop : IsCoprime (g : ℤ) m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : ¬ g ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 h1
  obtain ⟨a, b, hab⟩ := hcop
  refine le_antisymm (intCast_le_one s m) (not_lt.mp fun hlt => ?_)
  have e : ((a : s.v.adicCompletion (maximalRealSubfield L))) * (g : s.v.adicCompletion (maximalRealSubfield L)) +
      (b : s.v.adicCompletion (maximalRealSubfield L)) * (m : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : s.v.adicCompletion (maximalRealSubfield L))) hab
  have h1 : Valued.v ((a : s.v.adicCompletion (maximalRealSubfield L)) * (g : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v ((g : s.v.adicCompletion (maximalRealSubfield L))) := by gcongr; exact intCast_le_one s a
      _ < 1 := by rw [one_mul]; exact natCast_lt_one s g hg
  have h2 : Valued.v ((b : s.v.adicCompletion (maximalRealSubfield L)) * (m : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) := by gcongr; exact intCast_le_one s b
      _ < 1 := by rwa [one_mul]
  have h3 := lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h1 h2)
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

end Place

theorem mem_Umax_of_isLift : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ((g : 𝓞 L) ∈ s.w.asIdeal) → ∀ (x : Formalism.AUTREP.GAf L n) (γ : GL (Fin n) (ZMod g)), GlobalTheory.LabPin.IsLift s x γ → x ∈ ReciprocityTheory.Aut.Umax L n := by
  intro L _ _ _ n s g hp hg x γ hx
  obtain ⟨htriv, hred⟩ := hx
  haveI : Fact g.Prime := ⟨hp⟩
  set A : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) with hAdef
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
  let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    M.map (Int.castRingHom _)
  have hB : ∀ i j, Valued.v (B i j) ≤ 1 := fun i j => intCast_le_one s _
  have hAB : ∀ i j, Valued.v (A i j - B i j) < 1 := by
    intro i j
    have := hred i j
    have e : B i j = ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) :
        s.v.adicCompletion (maximalRealSubfield L)) := by
      change (((M i j : ℤ)) : s.v.adicCompletion (maximalRealSubfield L)) = _
      exact Int.cast_natCast _
    rw [e]
    exact this
  have hA : ∀ i j, Valued.v (A i j) ≤ 1 := by
    intro i j
    have e : A i j = (A i j - B i j) + B i j := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (hAB i j).le (hB i j))
  have hdetB : B.det = ((M.det : ℤ) : s.v.adicCompletion (maximalRealSubfield L)) :=
    (RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) M).symm
  have hMγ : M.map (Int.castRingHom (ZMod g)) = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext i j
    change (((M i j : ℤ)) : ZMod g) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdetM : ((M.det : ℤ) : ZMod g) = (γ : Matrix (Fin n) (Fin n) (ZMod g)).det := by
    rw [← hMγ]
    exact RingHom.map_det (Int.castRingHom (ZMod g)) M
  have hne : ¬ (g : ℤ) ∣ M.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hdetM]
    exact (Matrix.isUnits_det_units γ).ne_zero
  have hvB : Valued.v B.det = 1 := by rw [hdetB]; exact intCast_eq_one s g hp hg _ hne
  have hvA : Valued.v A.det = 1 := by
    have hd := det_sub_lt Valued.v A B hA hB hAB
    have e : A.det = (A.det - B.det) + B.det := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hvB]; exact hd), hvB]
  refine GlobalTheory.TSetFin.mem_Umax_of_loc s x htriv hA ?_
  intro i j
  rw [map_inv, Matrix.coe_units_inv, ← hAdef, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul,
    Ring.inverse_eq_inv', map_inv₀, hvA, inv_one, one_mul]
  exact adjugate_le_one Valued.v A hA i j

end GlobalTheory.LiftInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.PoincareInHH.Cut
open Matrix

variable {D : D7} (X : HidaSetting D)

theorem crd_injective' {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  rw [← toV_crd X y, ← toV_crd X y', h]

theorem eq_matEC {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {M : GL (Fin X.B.I.n) X.B.I.E}
    (h3 : ∀ y, X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) : n = matEC X M := by
  ext y
  exact crd_injective' X (by rw [h3, matE_crdC])

theorem nrat_iff (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n) :
    n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u := by
  constructor
  · intro hn
    have hgtop : Formalism.HermitianLatticesTheory.gmap n (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
      unfold Formalism.HermitianLatticesTheory.gmap; rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 n.surjective
    exact nLamNinf_holds D X u ⊤ x n hx ⟨⟨hn.1, hgtop⟩, hn.2.1, hn.2.2⟩
  · intro hν1
    obtain ⟨M, hM, hinf, -, h3⟩ := hx
    have hn := eq_matEC X h3
    subst hn
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (x.1 v) *ᵥ Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v y = Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.Pf.Vanish2.rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (x.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hν1 v
    refine ⟨matE_isomC X M hM, ?_, ?_⟩
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add, add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.NonRelPf

variable {D : D7} (X : HidaSetting D)

theorem sgUp_eq {E : Type} [Field E] [NumberField E] {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Formalism.L2.SG.PairVal.sgUp A = ∑ a : Fin r, A a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by omega)]
  rfl

theorem root_entry (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) (a : Fin D.R.rS) :
    (VS D).hT (X.fY a) (n (nxt X.eX (X.zu u) a)) = A a.castSucc a.succ := by
  have e : nxt X.eX (X.zu u) a = frame (lf D (X.Fu u)) a.succ := by
    show _ = (X.Fu u).fvec a.succ
    rw [fvec_succ, X.Fu_e, X.flagZVector]
  rw [e, hA, map_sum, Fin.sum_univ_castSucc]
  have h1 : ∀ b : Fin D.R.rS, frame (lf D (X.Fu u)) b.castSucc = X.eX b := by
    intro b
    show (X.Fu u).fvec b.castSucc = _
    simp only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
  have h2 : frame (lf D (X.Fu u)) (Fin.last D.R.rS) = X.zu u := by
    show (X.Fu u).fvec (Fin.last _) = _
    simp only [FlagG.fvec, Fin.snoc_last, X.flagZVector]
  simp only [map_smul, smul_eq_mul, h1, h2, hTfe, (X.zu_orth u a).2, mul_zero, add_zero, mul_ite, mul_one]
  rw [Finset.sum_ite_eq']
  simp

theorem psi_eq (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A) := by
  rw [psi_rat X u hx]
  simp only [root_entry X u n A hA]
  have hs : ∀ v, (∑ a : Fin D.R.rS, (Φ X v (A a.castSucc a.succ) + star (Φ X v (A a.castSucc a.succ)))) =
      X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A)) +
        star (X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A))) := by
    intro v
    rw [Finset.sum_add_distrib, ← star_sum, ← Φ_sum, ← sgUp_eq]
    rfl
  simp only [hs]
  rw [Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm _), RingEquiv.apply_symm_apply, X.g_eq]
  rfl

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

theorem ratLink_points : ∀ (D : D7) (X : HidaSetting D), (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃! x : X.B.I.GA, RatLink X x γ) ∧ (∀ x y γ δ, RatLink X x γ → RatLink X y δ → RatLink X (x * y) (γ * δ) ∧ RatLink X x⁻¹ γ⁻¹ ∧ (x.1 = y.1 → γ = δ)) ∧ ∀ (u : D.what₂.Word) x n, RatLink X x n → (n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u) ∧ (n ∈ NRat (lf D (X.Fu u)) → ∀ A : Formalism.L2.SG.PairVal.MatR D, (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) → X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A)) := by
  intro D X
  refine ⟨fun γ hγ => ?_, fun x y γ δ hx hy => ?_, fun u x n hx => ?_⟩
  · obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X γ hγ
    exact ⟨x, hx, fun y hy => Formalism.L2.SG.TermOp.Vanish.ratLink_unique X hy hx⟩
  · exact ⟨Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx hy, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx,
      Formalism.L2.SG.Pf.IdMeet.lin_eq_of_fst X hx hy⟩
  · exact ⟨nrat_iff X u hx, fun _ A hA => psi_eq X u hx A hA⟩

end GlobalTheory.RatIsomPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReproducingFormulaDiscreteSeriesTestGrowth
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Reproducing

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold rkR
  omega

theorem weight_condition (B : RowsAut) (h s : ℝ) (hn : 1 ≤ B.I.n) (hb : HBig B 40 h)
    (hs : s ≤ 2 * (B.I.n : ℝ) ^ 2) (v : InfinitePlace B.I.F) :
    rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h := by
  rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | h0
  · exact Or.inl h0
  right
  have h1 : (2 : ℝ) * rkR (B.I.ε v) ≤ B.I.n := by exact_mod_cast two_mul_rank_le _
  have h2 : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.2 (by exact_mod_cast h0)
  have h3 : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have h4 := hb v
  have h5 : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have h6 := mul_le_mul_of_nonneg_left h5 h2.le
  have h7 : 0 < Real.sqrt (rkR (B.I.ε v)) * (B.I.n : ℝ) ^ 2 := by positivity
  nlinarith

theorem inv_tau_pow_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    (tau1 I (x * g))⁻¹ ^ (2 * I.n ^ 2 * I.f) ≤
      (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * dSum I g.1) := by
  obtain ⟨hp, -, -, hl⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I hn
  have hf : (0 : ℝ) < I.f := by
    have : 0 < I.f := Module.finrank_pos
    exact_mod_cast this
  have h1 := (abs_le.1 (hl x g hg)).1
  have h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (dSum I g.1 / I.f) := by
    rw [← Real.exp_log (inv_pos.2 (hp (x * g))), ← Real.exp_log (inv_pos.2 (hp x)), ← Real.exp_add,
      Real.log_inv, Real.log_inv]
    exact Real.exp_le_exp.2 (by linarith)
  refine (pow_le_pow_left₀ (inv_pos.2 (hp _)).le h2 _).trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  field_simp

theorem isContRep_sum (B : RowsAut) {m : ℕ} (y : Fin m → B.I.L2 B.μf B.fund) (F : Fin m → B.I.GA → ℂ)
    (hF : ∀ i, IsContRep B (y i) (F i)) (c : Fin m → ℂ) :
    IsContRep B (∑ i, c i • y i) (fun x => ∑ i, c i * F i x) := by
  refine ⟨continuous_finset_sum _ fun i _ => continuous_const.mul (hF i).1, fun γ hγ x => ?_, ?_⟩
  · exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
  · have h1 := Lp.coeFn_finsetSum (univ : Finset (Fin m)) (fun i => c i • y i)
    have h2 : ∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), ∀ i, (c i • y i : B.I.L2 B.μf B.fund) x = c i * F i x :=
      ae_all_iff.2 fun i => by
        filter_upwards [Lp.coeFn_smul (c i) (y i), (hF i).2.2] with x hx hx'
        rw [hx, Pi.smul_apply, hx', smul_eq_mul]
    filter_upwards [h1, h2] with x hx hx'
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hx' i

theorem reproducing_formula : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B (T y) f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ∧ (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  intro B d h hd hn hdec hb hfin T hT y f hf
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨hp, htc, -, -⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties B.I hn
  obtain ⟨hphc, hphb, hphi⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d h hd hdec
  have hec : Continuous B.e := (GlobalTheory.rowsAut_idem_elementary B).2.2.2
  have hb' : HBig B 32 h := fun v => le_trans (by
    have : 0 ≤ (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
    nlinarith) (hb v)
  obtain ⟨u, F, -, hsp, hF, -, -, -, hbd⟩ := GlobalTheory.T.kernelB' B d h hd hn hdec hb' hfin T hT
  have hmem : T y ∈ Submodule.span ℂ (Set.range u) := by rw [hsp]; exact ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  obtain ⟨hext, huniq, -⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B (T y) f hf
  have hfe : (fun x => ∑ i, c i * F i x) = f := huniq _ (hc ▸ isContRep_sum B u F hF c)
  set N := 2 * B.I.n ^ 2 * B.I.f with hN
  have hτ : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ N := fun x => pow_nonneg (inv_pos.2 (hp x)).le _
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ N := by
    refine ⟨Real.sqrt ((∑ i, ‖c i‖ ^ 2) * kerC B d), Real.sqrt_nonneg _, fun x => ?_⟩
    have h1 := hbd c x
    rw [congrFun hfe x, show 4 * B.I.n ^ 2 * B.I.f = N * 2 by rw [hN]; ring, pow_mul, ← mul_assoc] at h1
    have h2 := Real.le_sqrt_of_sq_le h1
    rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (hτ x)] at h2
  let Φ : B.I.GA → ℝ := fun g =>
    C * (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖)
  have hm0 : ∀ g, 0 ≤ majPh B d h g := fun g => (norm_nonneg _).trans (hphb g)
  have hΦ0 : ∀ g, 0 ≤ Φ g := fun g =>
    mul_nonneg hC0 (mul_nonneg (mul_nonneg (hm0 _) (Real.exp_pos _).le) (norm_nonneg _))
  have hΦi : Integrable Φ (B.I.muA B.μf) :=
    (Integrable.mul_prod (hphi _ (by positivity) (weight_condition B h _ hn hb le_rfl))
      B.Re_spec.1.norm).const_mul C
  have hΦ : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ N * Φ g := by
    intro x g
    by_cases he : B.e g.2 = 0
    · rw [phe, he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hτ x) (hΦ0 g)
    have hg : g.2 ∈ B.I.Kset := B.e_adm.2.2.2.2.1 _ he
    have h1 := (hC (x * g)).trans (mul_le_mul_of_nonneg_left (inv_tau_pow_le B.I hn x g hg) hC0)
    rw [norm_mul, phe, norm_mul]
    calc _ ≤ (majPh B d h g.1 * ‖B.e g.2‖) *
          (C * ((tau1 B.I x)⁻¹ ^ N * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hphb _) (norm_nonneg _)) h1 (norm_nonneg _)
            (mul_nonneg (hm0 _) (norm_nonneg _))
      _ = _ := by simp only [Φ]; ring
  refine ⟨⟨C, hC⟩, ⟨Φ, hΦi, hΦ⟩, fun x => (congrFun (huniq (fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf))
    ⟨?_, fun γ hγ x => ?_, ?_⟩) x).symm⟩
  · have hpc : Continuous (phe B d) := (hphc.comp continuous_fst).mul (hec.comp continuous_snd)
    have htN : Continuous fun x => (tau1 B.I x)⁻¹ ^ N := (htc.inv₀ fun x => (hp x).ne').pow _
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    refine continuousAt_of_dominated (bound := fun g => ((tau1 B.I x₀)⁻¹ ^ N + 1) * Φ g)
      (Filter.Eventually.of_forall fun x => ?_) ?_ (hΦi.const_mul _) (Filter.Eventually.of_forall fun g => ?_)
    · exact (hpc.mul (hf.1.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · filter_upwards [htN.continuousAt.eventually_lt continuousAt_const (lt_add_one ((tau1 B.I x₀)⁻¹ ^ N))]
        with x hx
      exact Filter.Eventually.of_forall fun g => (hΦ x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))
    · exact (continuous_const.mul (hf.1.comp (continuous_id.mul continuous_const))).continuousAt
  · simp only [mul_assoc, hf.2.1 γ hγ]
  · have hi : Integrable (ph B d) (muInf B.I) := by
      refine (hphi 0 le_rfl (weight_condition B h _ hn hb (by positivity))).mono' hphc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => ?_)
      simpa using hphb g
    have hproj := ((GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hd hi).2.2.2 T hT).1
    have hTT : T (T y) = T y := congrArg (fun A : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => A y) hproj.1
    have h1 := (GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT (T y)).2
    rw [hTT] at h1
    refine h1.trans (Filter.Eventually.of_forall fun x => integral_congr_ae ?_)
    filter_upwards [(measurePreserving_mul_left (B.I.muA B.μf) x).quasiMeasurePreserving.ae hext] with g hg
    rw [hg]

end GlobalTheory.Reproducing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory.SplitProj

theorem proj_eq_lift_compAt (L : Type) [Field L] [NumberField L] (s : SplitPlace L) (x : AL L) :
    s.proj x = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (compAt L s.v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem proj_eq_zero_of_compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L)
    (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  intro L _ _ s a h
  rw [proj_eq_lift_compAt, h, map_zero]

end GlobalTheory.SplitProj
end

