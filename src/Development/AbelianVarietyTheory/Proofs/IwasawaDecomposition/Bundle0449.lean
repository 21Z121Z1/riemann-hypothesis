import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ColAd

theorem exists_K1_isPtOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ g hg c
  classical
  have hcc : ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  obtain ⟨p, hp⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc c hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hp.deco
  obtain ⟨g', hg', c1, c2, c3⟩ := PtExist.exists_modify (fun P hP => (hQ P hP).2.2.2.2) hg (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  have hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hP with hP | hP
      · exact (hQ P h).1 hP
      · exact (hQ P h).2.1 hP
    · have := hQ _ h
      rw [hcc] at this
      rcases hP with hP | hP
      · exact this.2.2.1 hP
      · exact this.2.2.2.1 hP
  have hpt : IsPtOf hc g' p := by
    refine ⟨hg', hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
    · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
      rw [← hN] at hv
      have ho := hoff P.1 (Or.inl P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv), e]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [← hN] at hv
      have ho := hoff P.1 (Or.inr P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv)]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [c2 _ P.2, ptFr_of_mem p (hQ P.1 P.2).2.1 P.2]
      rfl
  have hd : decoRaw ST SG g = decoRaw ST SG g' := hp.deco.trans (near_of_isPtOf hpt c).deco.symm
  refine ⟨g⁻¹ * g', mem_principal_of_same_decoration hc n ST SG hg hg' hd, fun P => ?_, p, by rwa [mul_inv_cancel_left]⟩
  have e : locM P.1 g' = ratM P.1 (p.fr P) := Matrix.ext fun i j => hpt.fr P i j
  rw [locM_mul, e]
  exact hp.fr P

end GlobalTheory.Mem.ColAd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelOfLinearMapStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_of_linear_map : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W), ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' → GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka := by
  first | exact @GlobalTheory.PtId.OneScalar.exists_scalar | exact GlobalTheory.PtId.OneScalar.exists_scalar | (intros; apply GlobalTheory.PtId.OneScalar.exists_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta ∧ ∃ io, ({ R with ioP := io } : RealDat D A Ks).thP_ioP := by
  first | exact @GlobalTheory.JointHarm.exists_ioP | exact GlobalTheory.JointHarm.exists_ioP | (intros; apply GlobalTheory.JointHarm.exists_ioP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLevelShrink

theorem isCompact_of_isOpen_subgroupOf {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H U A : Subgroup G) (hAU : A ≤ U) (hUH : U ≤ H) (hU : IsCompact (U : Set G))
    (hA : IsOpen {x : H | (x : G) ∈ A}) : IsCompact (A : Set G) := by
  haveI : ContinuousMul H := inferInstanceAs (ContinuousMul H.toSubmonoid)
  have hcl : IsClosed ((A.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ hA
  have hU' : IsCompact (Subtype.val ⁻¹' (U : Set G) : Set H) := by
    rw [Subtype.isCompact_iff]
    convert hU using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUH hx⟩, hx, rfl⟩
  have h2 := hU'.inter_right hcl
  rw [Subtype.isCompact_iff] at h2
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hUH (hAU hx)⟩, ⟨hAU hx, hx⟩, rfl⟩
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy

end GlobalTheory.StepLevelShrink

namespace GlobalTheory.StepLevelShrink

theorem exists_stepLevel_shrink : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  intro F E _ _ _ _ _ σ n J T f bad S Qv A ψ hAU hQT hloc hopen hψ
  classical
  have hSU : ∀ y ∈ S.U, y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) y ∈ S.Uloc v :=
    fun y hy => (S.U_eq y).1 hy
  let L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v
      Uloc_le := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_le v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_le v
      Uloc_lev := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_lev v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_lev v
      Uloc_hyp := by
        intro v hv hT
        have hb : v ∉ bad := fun h => hv (Or.inl h)
        have hq : v ∉ Qv := fun h => hv (Or.inr (Finset.mem_coe.2 h))
        simp only [if_neg hq]
        exact S.Uloc_hyp v hb hT
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        have hq : v ∉ Qv := fun hq => hQT v hq h
        simp only [if_neg hq]
        exact S.UlocAlt v h
      U := A
      U_eq := by
        intro x
        constructor
        · intro hx
          refine ⟨(hSU x (hAU hx)).1, fun v => ?_⟩
          by_cases hq : v ∈ Qv
          · simp only [if_pos hq]
            exact ⟨x, hx, rfl⟩
          · simp only [if_neg hq]
            exact (hSU x (hAU hx)).2 v
        · rintro ⟨hP, hv⟩
          have hxS : x ∈ S.U := by
            refine (S.U_eq x).2 ⟨hP, fun v => ?_⟩
            have h1 := hv v
            by_cases hq : v ∈ Qv
            · simp only [if_pos hq] at h1
              obtain ⟨y, hy, hyx⟩ := h1
              rw [← hyx]
              exact (hSU y (hAU hy)).2 v
            · simp only [if_neg hq] at h1
              exact h1
          refine hloc x hxS fun v hq => ?_
          have h1 := hv v
          simp only [if_pos hq] at h1
          obtain ⟨y, hy, hyx⟩ := h1
          exact ⟨y, hy, hyx.symm⟩
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
        exact isCompact_of_isOpen_subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U A hAU
          (fun y hy => (hSU y hy).1) S.U_compact hopen
      U_open := hopen
      chi := (S.chi.comp (Subgroup.inclusion hAU)) * ψ
      chi_triv := by
        intro x hx
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply,
          S.chi_triv (Subgroup.inclusion hAU x) (fun v hv => hx v (Or.inl hv)),
          hψ x (fun v hv => hx v (Or.inr (Finset.mem_coe.2 hv))), one_mul] }
  refine ⟨L, rfl, rfl, fun v hv => by
    show (if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v) = S.Uloc v
    exact if_neg hv, ?_⟩
  intro x x' x'' h1 h2
  show S.chi (Subgroup.inclusion hAU x) * ψ x = S.chi x' * ψ x''
  have e1 : Subgroup.inclusion hAU x = x' := Subtype.ext h1
  have e2 : x = x'' := Subtype.ext h2
  rw [e1, e2]

end GlobalTheory.StepLevelShrink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwUnit

section Diag

variable {E : Type} [Field E]

open Classical in

def dEnt (n : ℕ) (π : E) (i : Fin n) : E := if i.1 + 1 = n then (if π = 0 then 1 else π) else 1

theorem dEnt_ne (n : ℕ) (π : E) (i : Fin n) : dEnt n π i ≠ 0 := by
  unfold dEnt
  split_ifs with h1 h2 <;> simp_all

def dAut (n : ℕ) (π : E) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero E E (dEnt n π i) (dEnt_ne n π i)

theorem dAut_apply (n : ℕ) (π : E) (x : Fin n → E) (i : Fin n) : dAut n π x i = dEnt n π i * x i := rfl

end Diag

theorem exists_tw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ π hπ
  classical
  have hQc : ∀ P ∈ Q, conjPrime₂ P ∉ Q := fun P hP => (hQ P hP).2.2.2.2
  have hπ0 : ∀ P ∈ Q, (π : E) ≠ 0 := fun P hP h => hπ P hP (by
    have : π = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [this]; exact P.asIdeal.zero_mem)
  have hval : ∀ P ∈ Q, ∀ i : Fin n, P.valuation E (dEnt n (π : E) i) = 1 := by
    intro P hP i
    unfold dEnt
    rw [if_neg (hπ0 P hP)]
    split_ifs
    · exact le_antisymm (HeightOneSpectrum.valuation_le_one _ π)
        (not_lt.1 fun h => hπ P hP ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))
    · exact map_one _
  have hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat (1 : GL (Fin n) (AfE F E)) (stdLat E n))
      (dAut n (π : E)) := by
    intro P hP x
    rw [globLat_one_std]
    show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
    rw [mem_localization_standardLattice, mem_localization_standardLattice]
    simp only [dAut_apply, CharValCompare.intAt_iff, map_mul, hval P hP, one_mul]
  obtain ⟨g, hg, c1, c2, c3⟩ := PtExist.exists_modify (hc := hc) hQc (one_mem (UAd hc n)) (fun _ => dAut n (π : E)) hfr

  have hST : ∀ P ∈ ST, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).1 hP, fun h => (hQ _ h).2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hSG : ∀ P ∈ SG, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).2.1 hP, fun h => (hQ _ h).2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hb := isPtOf_base (F := F) hc (n := n) (ST := ST) (SG := SG) (Q := (∅ : Finset (HeightOneSpectrum (𝓞 E))))
  have hpt : IsPtOf hc g (DecoF.base E n ST SG (∅ : Finset (HeightOneSpectrum (𝓞 E)))) := by
    refine ⟨hg, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · have h := c1
      rw [globLat_one_std] at h
      exact h
    · rw [c3 P.1 (hST P.1 P.2).1 (hST P.1 P.2).2 x i]
      exact hb.f P x hx i hi
    · rw [c3 w.1 (hSG w.1 w.2).1 (hSG w.1 w.2).2 x i]
      exact hb.be w x hx i
  have hd := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (DecoF.base E n ST SG ∅) rfl).1 hpt
  have hK := mem_principal_of_same_decoration hc n ST SG (one_mem _) hg (by rw [decoRaw_one, ← hd.2]; rfl)
  rw [inv_one, one_mul] at hK
  refine ⟨g, hK, fun P i j => ?_, fun w hw hw' i j => ?_⟩
  · rw [c2 P.1 P.2 i j]
    congr 1
    show dAut n (π : E) (Pi.single j 1) i = _
    rw [dAut_apply]
    unfold dEnt
    rw [if_neg (hπ0 P.1 P.2)]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e1 : ∀ i j, adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        if i = j then 1 else 0 := by
      intro i j
      have h := c3 w hw hw' (Pi.single j 1) i
      have hv : (fun k => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j (1 : E) : Fin n → E) k)) =
          Pi.single j 1 := by
        ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have h' : adAt F w ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) =
          adAt F w ((((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) := by
        rw [← hv]; exact h
      rw [inv_one, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_single_one] at h'
      have h'' : adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
          adAt F w ((Pi.single j 1 : Fin n → AfE F E) i) := h'
      rw [h'', Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hMi : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F w) = 1 := by
      ext a b
      rw [Matrix.map_apply, e1, Matrix.one_apply]
    have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)) * ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      have h := congrArg (fun M => M.map (adAt F w)) hgg
      simp only [Matrix.map_mul, hMi, mul_one] at h
      rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
    have h := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at h
    exact h

end GlobalTheory.Mem.Col2.TwUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_conj_integralFrame : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | exact GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KeepLevel

open GlobalTheory.Mem GlobalTheory.Mem.Th GlobalTheory.ChainEquiv

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank}

theorem levChi_withP (P : LevelP L.Pg L.r ℂ) (p : P.H) {κ : GA D V} (hκ : IsLevelLift V β L p κ) :
    levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]

theorem eigen_of_hasType {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ} (hf : HasType V β (withP L P) f) (p : P.H) {κ : GA D V}
    (hκ : IsLevelLift V β L p κ) (h : GA D V) : ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ) := by
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2.symm ▸ p.2
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [hf κ ⟨hκ.1, hκ.2.1, hp⟩ h, levChi_withP P p hκ]
  field_simp

theorem hasType_of_eigen {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ}
    (hf : ∀ (p : P.H) κ, IsLevelLift V β L p κ → ∀ h, ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ)) :
    HasType V β (withP L P) f := by
  intro κ hκ h
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2
  have hl : IsLevelLift V β L (⟨_, hp⟩ : P.H) κ := ⟨hκ.1, hκ.2.1, rfl⟩
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [levChi_withP P _ hl, mul_right_comm, hf _ κ hl h]
  field_simp

theorem mem_mult_of_level {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {X : MMap M} (hX : X ∈ Mult θ M J χ)
    (h : ∀ v, ∀ k ∈ J', ∀ g, X v (g * k) = χ' k * X v g) : X ∈ Mult θ M J' χ' :=
  have a := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ X).1 hX
  Submodule.subset_span ⟨a.aut, a.cusp, h, a.equiv, a.cont⟩

theorem hasType_of_comm (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {f : GA D V → ℂ}
    (h1 : HasType V β (flag1L L) f) (h2 : HasType V β (flag1L L) (e f)) (hf : HasType V β (withP L P) f)
    (hc : ∀ g, e (actL V β L g f) = actL V β L g (e f)) : HasType V β (withP L P) (e f) := by
  refine IsPLevel.hasType ⟨h2, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p
  have a : actL V β L p f = ((P.chi p : ℂˣ) : ℂ) • f := funext fun h =>
    (level_action_spec h1 ⟨κ, hκ⟩ κ hκ h).trans (eigen_of_hasType hf p hκ h).symm
  exact (hc p).symm.trans ((congrArg e a).trans (e.map_smul _ f))

end General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem mem_lvlPart_iff (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) (U : R.CC t j) :
    U ∈ lvlPart R P t j ↔ ∀ p : P.H, Rel R t p j U (((P.chi p : ℂˣ) : ℂ) • U) := by
  constructor
  · intro hU p κ hκ v h
    have a : (U : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ∈ MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P))
      (levChi _ (R.βY j) (R.datYt t j P)) := (mem_multT R.θ (R.MY j) _ _ _).2 hU
    exact eigen_of_hasType (L := R.datYt t j R.triv) (P := P) (multT_value _ _ _ _ _ a v).2 p hκ h
  · intro hU
    refine mem_mult_of_level ((mem_multT R.θ (R.MY j) _ _ _).1 U.2) fun v => ?_
    exact hasType_of_eigen (L := R.datYt t j R.triv) (P := P) fun p κ hκ h => hU p κ hκ (PiTensorProduct.tprod ℂ v) h

theorem rel_ioY (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hY : R.models_νY)
    (hY' : R.models_νY') (hc : R.IsChain) (t : T) (g0 : G0 R.Pg D.R.r) (k : ℕ) (hn : k + 1 < D.R.m) (U U' : R.CC t (k + 1))
    (hU : Rel R t g0 (k + 1) U U') : Rel R t g0 k (R.ioY t k U) (R.ioY t k U') := by
  have hk : k < D.R.m := by omega
  intro κ hκ v g
  obtain ⟨κ', hκ'⟩ := lifts_chain R.toLevCh _ hl t (k + 1) hn g0
  exact step R.ψ R.θ hi _ _ (R.ωY t k) (hc.ωY t k hn) _ _ _ _ (R.vY t k) (hc.ptY t k hn) (R.MY k)
    (R.βY k) (R.datYt t k R.triv) rfl _ (meas_chain hY hY' t k hk).1 _ (meas_chain hY hY' t k hk).2
    (GlobalTheory.MultFinite.schurMult hD _ _)
    (R.ItY k) (hc.ItY t k hn).ne (R.CC t (k + 1)) (fun U w => (multT_value _ _ _ _ _ U.2 w).1)
    (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) _ (meas_chain hY hY' t (k + 1) hn).1 _ (meas_chain hY hY' t (k + 1) hn).2
    (R.ioY t k) (hc.ioY t k (by omega)) g0 κ hκ g0 κ' hκ' _
    (GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hl hi hc.ωY hc.vY t k hn g0 κ κ' hκ hκ') U U' (hU κ' hκ') v g

theorem ioY_mem (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hY : R.models_νY)
    (hY' : R.models_νY') (hc : R.IsChain) (P : LevelP R.Pg D.R.r ℂ) (t : T) (k : ℕ) (hn : k + 1 < D.R.m) (U : R.CC t (k + 1))
    (hU : U ∈ lvlPart R P t (k + 1)) : R.ioY t k U ∈ lvlPart R P t k :=
  (mem_lvlPart_iff P t k _).2 fun p =>
    (R.ioY t k).map_smul _ U ▸ rel_ioY hD hl hi hY hY' hc t p k hn U _ ((mem_lvlPart_iff P t (k + 1) U).1 hU p)

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hr : R.grp_record) (P : LevelP R.Pg D.R.r ℂ) (t : T)
    {X : MMap (R.MY 0)} (hX : X ∈ multAt R P t 0) : postOn (R.MY 0) R.e0 X ∈ R.EEat P := by
  have h0 := multAt_le R P t 0 hX
  rw [multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 X ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (GlobalTheory.ProjectedLift.eC_conv R hr) h0
  refine ⟨mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (X v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 h0).lev v
  refine hasType_of_comm (L := R.dat0 R.triv) (P := P) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 hX).lev v) fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact (GlobalTheory.ProjComm.proj_comm R hl hr).1 g _ a0

theorem topLift_mem (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hr : R.grp_red_R) (hM : R.IsModels) (hc : R.IsChain)
    (Q : Subgroup G) (ψ : Q →* D.what₂.LLˣ) (t : T) (f : (A.MtildeCSD t).Forms)
    (hf : f ∈ lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) Q ψ) :
    topLift R t (R.jX t f) ∈ lvlPart R (levPOf R.eG D.what₂.embLL Q ψ) t (D.R.m - 1) := by
  refine (mem_lvlPart_iff _ t _ _).2 fun p => ?_
  refine (GlobalTheory.FormAction.act_eq_translate R hr hM.jX t (R.eG.symm p) f).elim fun κ h => ?_
  have hκ : IsLevelLift D.sp.X' R.βX (R.datXt t) p.1 κ :=
    (congrArg (fun g => IsLevelLift D.sp.X' R.βX (R.datXt t) g κ) (R.eG.apply_symm_apply p.1)).mp h.1
  have a : Rel R t p (D.R.m - 1) (topLift R t (R.jX t f)) (topLift R t (R.jX t ((A.fam.R t).r (R.eG.symm p) f))) :=
    rel_ioX hl hM.inf hM.νY hM.νY' hc hM.νX hM.cX hM.HX (fun _ _ _ => GlobalTheory.MultFinite.schurMult hD _ _) t p κ hκ _ _ h.2
  have e : topLift R t (R.jX t ((A.fam.R t).r (R.eG.symm p) f)) =
      (((levPOf R.eG D.what₂.embLL Q ψ).chi p : ℂˣ) : ℂ) • topLift R t (R.jX t f) :=
    (congrArg (fun z => topLift R t (R.jX t z)) (hf ⟨R.eG.symm p, p.2⟩)).trans
      ((congrArg (topLift R t) ((R.jX t).map_smulₛₗ _ f)).trans ((topLift R t).map_smul _ _))
  exact (congrArg (Rel R t p (D.R.m - 1) (topLift R t (R.jX t f))) e).mp a

theorem keepsLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool), GlobalTheory.Published.CuspRapidDecay → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsChain → GlobalTheory.Mem.Th.KeepsLevel R F b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F b hD hl hg hM hc t
  exact ⟨fun U hU => goodProjector_levelMultiplicitySpace_mem_goodRows hl hM.inf hg.record _ t (ioY_mem hD hl hM.inf hM.νY hM.νY' hc _ t 0 D.R.two_le_m U hU),
    fun j _ hj U hU => ioY_mem hD hl hM.inf hM.νY hM.νY' hc _ t j hj U hU,
    fun f hf => topLift_mem hD hl hg.red_R hM hc _ _ t f hf⟩

theorem exists_multTie {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (hF : GlobalTheory.Published.HarishChandraFinite)
    (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hg : R.IsGrp F) (hM : R.IsModels) (hc : R.IsChain)
    (hinj : Function.Injective tup) (Y : SideTie R F tup b S) :
    ∃ (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) (Y' : SideTie R F tup b (withChain S c)),
      Y'.eE = Y.eE ∧ Y'.eA = Y.eA ∧ (∀ μ, (withChain S c).iota μ = S.iota μ) ∧ Nonempty (MultTie Y') :=
  GlobalTheory.Mem.Th.exists_multTie hF hD hM hc.Th (keepsLevel D G Pl0 T A Ks R F b hD hl hg hM hc) hinj Y

end GlobalTheory.KeepLevel

end
end

