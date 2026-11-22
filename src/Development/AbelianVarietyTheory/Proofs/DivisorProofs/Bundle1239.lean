import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import GroundTheory.AutomorphicForms.GLnLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReduction
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatSep

theorem nilp_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilp_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilp_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem exists_lt_pow (x B : WithZero (Multiplicative ℤ)) (hx : 1 < x) : ∃ m : ℕ, B < x ^ m := by
  obtain ⟨k, hk⟩ := MulArchimedean.arch B hx
  refine ⟨k + 1, hk.trans_lt ?_⟩
  have h0 : x ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))
  rw [pow_succ]
  simpa using mul_lt_mul_of_pos_left hx (zero_lt_iff.2 h0)

theorem integral_of_commute_sep : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ w n P₀ hP A s hA hAc hsA hBd i j
  obtain ⟨B, hB⟩ := hBd
  have memO : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E ↔ Valued.v x ≤ 1 :=
    fun x => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  by_contra hij
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨⟨i₀, j₀⟩, hmax⟩ := Finite.exists_max (fun p : Fin n × Fin n => Valued.v (s p.1 p.2))
  have hc1 : 1 < Valued.v (s i₀ j₀) := by
    have : 1 < Valued.v (s i j) := not_le.1 (fun h => hij ((memO _).2 h))
    exact this.trans_le (hmax (i, j))
  have hvc : Valued.v (s i₀ j₀) ≠ 0 := ne_of_gt (zero_lt_one.trans hc1)
  have hc0 : s i₀ j₀ ≠ 0 := fun h => hvc (by rw [h, map_zero])
  set c := s i₀ j₀ with hcdef
  set u := c⁻¹ • s with hudef
  have hu : ∀ k l, u k l ∈ w.adicCompletionIntegers E := by
    intro k l
    rw [memO]
    simp only [u, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvc), mul_one]
    exact hmax (k, l)
  let A₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨A k l, hA k l⟩
  let u₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨u k l, hu k l⟩
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hA₀ : A₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = A := by
    ext; rfl
  have hu₀ : u₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = u := by
    ext; rfl
  have hcomm : Commute A₀ u₀ := by
    apply Matrix.map_injective hinj
    show (A₀ * u₀).map _ = (u₀ * A₀).map _
    rw [Matrix.map_mul, Matrix.map_mul, hA₀, hu₀]
    exact ((hsA.smul_left c⁻¹).symm).eq
  have hcp : A₀.charpoly = P₀ := by
    apply Polynomial.map_injective _ hinj
    rw [← Matrix.charpoly_map, hA₀, hAc]
  obtain ⟨m, hm⟩ := exists_lt_pow (Valued.v c) B hc1
  have hsmall : ∀ k l, Valued.v ((u ^ m) k l) < 1 := by
    intro k l
    rw [hudef, _root_.smul_pow, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_inv₀, inv_pow,
      inv_mul_lt_iff₀ (pow_pos (zero_lt_iff.2 hvc) _), mul_one]
    exact (hB m k l).trans_lt hm
  have hnil : IsNilpotent (u₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))) := by
    refine ⟨m, ?_⟩
    rw [← Matrix.map_pow]
    ext k l
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨y, hy⟩
    have e : (((u₀ ^ m) k l : w.adicCompletionIntegers E) : w.adicCompletion E) = (u ^ m) k l := by
      rw [← hu₀, ← Matrix.map_pow]; rfl
    have h1 := hsmall k l
    rw [← e, ← hy] at h1
    have h2 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
      have hy1 : ((y : w.adicCompletionIntegers E) : w.adicCompletion E) *
          (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
        first
          | exact congrArg Subtype.val y.mul_inv
          | exact_mod_cast congrArg Subtype.val y.mul_inv
          | simp
      rw [← map_mul, hy1, map_one]
    have h3 := (memO _).1 (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E)).2
    have h4 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) h1
    rw [h2] at h4
    exact lt_irrefl _ h4
  have hsep : (A₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))).charpoly.Separable := by
    rw [Matrix.charpoly_map, hcp]
    exact Polynomial.Separable.map hP
  have h0 := nilp_eq_zero_of_commute_sep hsep hnil
    (hcomm.map (IsLocalRing.residue (w.adicCompletionIntegers E)).mapMatrix)
  have hone : u₀ i₀ j₀ = 1 := by
    apply Subtype.ext
    show c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc0
  have := congrFun (congrFun h0 i₀) j₀
  simp only [Matrix.map_apply, Matrix.zero_apply, hone, map_one] at this
  exact one_ne_zero this

end GlobalTheory.IntMatSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLevel

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mem_levi_flag_of_mem_parabolic (P : LevelP L.Pg L.r ℂ) {k : GA D V} (hk : k ∈ levG V β (flag1L L)) :
    k ∈ levG V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := by
    have : rTup β L (finE V k) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2.2
    exact Subgroup.mem_bot.1 this
  refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
  · show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · unfold levChi
    rw [levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem isPLevel_of_hasType (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ}
    (hF : HasType V β (withP L P) F) : IsPLevel V β L P F := by
  have h1 : HasType V β (flag1L L) F := fun k hk h => by
    rw [hF k (mem_levi_flag_of_mem_parabolic P hk).1, (mem_levi_flag_of_mem_parabolic P hk).2]
  refine ⟨h1, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p.1
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hm : κ ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
    unfold levChi
    rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  funext h
  rw [level_action_spec h1 ⟨κ, hκ⟩ κ hκ h, hF κ hm, hc]
  field_simp

theorem postOn_actL_mem (g0 : G0 L.Pg L.r) {X : MMap M}
    (hT : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (actL V β L g0) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have hU : ∀ v, postOn M (actL V β L g0) X v = actG0 V β L g0 (X v) := fun _ => rfl
  by_cases hex : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hex.choose_spec
    have e : postOn M (actL V β L g0) X = (levChi V β (flagL L) hex.choose)⁻¹ • heckeOn M {hex.choose} X := by
      ext v g
      rw [hU, actG0, dif_pos hex]
      simp [heckeOn, postOn_apply, heckeLin_apply]
    rw [e]
    refine Submodule.smul_mem _ _ ?_
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT (fun k hk => ?_) fun v k hk g => ?_
    · rw [Finset.mem_singleton.1 hk]
      exact hκ.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.FlagAction.conj_mem_flag1 hκ hk
      simp only [heckeLin_apply, Finset.sum_singleton]
      rw [← h2, ← hT.lev v _ h1]
      group
  · have e : postOn M (actL V β L g0) X = 0 := by
      ext v g
      rw [hU, actG0, dif_neg hex]
      rfl
    rw [e]
    exact zero_mem _

theorem postOn_gaL_mem_goodPart (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    (hcomm : ∀ g F, HasType V β (flag1L L) F →
      gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F))
    (P : LevelP L.Pg L.r ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P)) (gaL V β L eG c) := by
  have hX1 : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    GlobalTheory.ProjectedLift.mult_mono (fun k hk => mem_levi_flag_of_mem_parabolic P hk) hX
  have hY : postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
    have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
      ext v h
      simp [gaL, postOn_apply]
    rw [e]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (postOn_actL_mem _ hX1)
  rw [mem_goodPart]
  refine ⟨?_, fun v => GlobalTheory.ProjectedLift.gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX1 v)⟩
  have hY' := (GlobalTheory.MultMem.mem_mult_iff ..).1 hY
  refine (GlobalTheory.MultMem.mem_mult_iff ..).2 ⟨hY'.aut, hY'.cusp, fun v => ?_, hY'.equiv, hY'.cont⟩
  have hP := isPLevel_of_hasType hL (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)
  have hQ : IsPLevel V β L P (gaL V β L eG c (X v)) := by
    refine ⟨hY'.lev v, fun p => ?_⟩
    have e1 : actL V β L p.1 (X v) = ((P.chi p : ℂˣ) : ℂ) • X v := hP.2 p
    have e2 := hcomm (eG.symm p.1) _ hP.1
    rw [MulEquiv.apply_symm_apply, e1, map_smul] at e2
    exact e2.symm
  exact hQ.hasType

end Act

theorem proj_mem_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ), ∀ U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)), postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U ∈ R.Wat i (sg0 D A) P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hv i P U hU
  have hL : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := h.βW i
    refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ hv
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := by
    rw [hs]; exact GlobalTheory.ProjectedLift.eC_conv R hr
  exact postOn_gaL_mem_goodPart (L := R.datWp i R.triv) hL R.eG _ hc
    ((GlobalTheory.ProjComm.proj_comm R h hr).2 i (sg0 D A)) P hU

end GlobalTheory.GoodProjLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open ValuativeRel GroundTheory.Automorphic.GLnLocal
open scoped Pointwise

noncomputable section
namespace GlobalTheory.StabInt

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem mem_O_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ w.adicCompletionIntegers E := by
  show _ ↔ Valued.v x ≤ 1
  simp only [Valuation.mem_integer_iff]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := (Valuation.Compatible.vle_iff_le (v := Valued.v) x 1)
  rw [map_one] at h1
  rw [← h1]
  exact Iff.symm (Valuation.vle_one_iff (valuation (w.adicCompletion E)))

theorem mem_integralGL_of_mem_KGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    g ∈ integralGL (w.adicCompletion E) n := by
  obtain ⟨u, rfl⟩ := hg
  rw [mem_integralGL_iff]
  refine ⟨fun i j => (mem_O_iff _).2 (u i j).2, fun i j => (mem_O_iff _).2 ?_⟩
  rw [← map_inv]
  exact ((u⁻¹ : GL (Fin n) (Ov E w)) i j).2

theorem mem_KGL_of_mem_integralGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ integralGL (w.adicCompletion E) n) :
    g ∈ GlobalTheory.LFun.KGL w n := by
  rw [mem_integralGL_iff] at hg
  have h1 : ∀ i j, g.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.1 i j)
  have h2 : ∀ i j, g⁻¹.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.2 i j)
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_integralGL_of_conj (N t g : GL (Fin n) (w.adicCompletion E))
    (hN : N ∈ integralGL (w.adicCompletion E) n)
    (hsep : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1)
    (htN : t * N = N * t) (ht' : g⁻¹ * t * g ∈ integralGL (w.adicCompletion E) n)
    (hN' : g⁻¹ * N * g ∈ integralGL (w.adicCompletion E) n) : t ∈ integralGL (w.adicCompletion E) n := by
  set F := w.adicCompletion E
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist F :=
    inferInstanceAs (@IsUltrametricDist F (Valued.toNormedField F (WithZero (Multiplicative ℤ))).toDist)
  have hO : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ 𝒪[F] := fun x =>
    (Valued.toNormedField.norm_le_one_iff).trans (mem_O_iff x).symm
  have hs : N.val.charpoly.Separable := by
    obtain ⟨u, v, -, -, h⟩ := hsep
    exact ⟨u, v, h⟩
  have hsep' : ∃ u v : Polynomial F, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.val.charpoly + v * Polynomial.derivative N.val.charpoly = 1 := by
    obtain ⟨u, v, hu, hv, h⟩ := hsep
    exact ⟨u, v, fun i => (hO _).2 ((mem_O_iff _).2 (hu i)), fun i => (hO _).2 ((mem_O_iff _).2 (hv i)), h⟩
  have hNi : ∀ i j, ‖N.val i j‖ ≤ 1 := fun i j => (hO _).2 ((mem_integralGL_iff F n).1 hN |>.1 i j)
  have hN'i : ∀ i j, ‖((g.val)⁻¹ * N.val * g.val) i j‖ ≤ 1 := by
    intro i j
    have := ((mem_integralGL_iff F n).1 hN').1 i j
    rw [← Matrix.coe_units_inv]
    exact (hO _).2 this
  obtain ⟨c, hcu, hcN, hy, hdet⟩ := GlobalTheory.IntConj.exists_commuting_mul_integral F n N.val g.val hNi hsep' g.isUnit hN'i
  set cU := hcu.unit with hcU
  have hcUv : (cU : Matrix (Fin n) (Fin n) F) = c := rfl
  have hcadj : c ∈ Algebra.adjoin F {N.val} := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N.val c hs hcN
  have htNv : Commute t.val N.val := by
    show t.val * N.val = N.val * t.val
    have := congrArg Units.val htN
    simpa [Units.val_mul] using this
  have htc : Commute t.val c := Algebra.commute_of_mem_adjoin_singleton_of_commute hcadj htNv
  have htcU : t * cU = cU * t := Units.ext (by simpa [Units.val_mul, hcUv] using htc.eq)
  set yU := cU⁻¹ * g with hyU
  have hyv : (yU : Matrix (Fin n) (Fin n) F) = c⁻¹ * g.val := by
    rw [hyU, Units.val_mul, Matrix.coe_units_inv, hcUv]
  have hyO : yU ∈ integralGL F n := by
    rw [mem_integralGL_iff]
    have h1 : ∀ i j, (yU : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := fun i j => by
      rw [hyv]; exact (hO _).1 (hy i j)
    refine ⟨h1, fun i j => ?_⟩
    let y₀ : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, h1 i j⟩
    have hy₀ : (RingHom.mapMatrix (𝒪[F]).subtype) y₀ = (yU : Matrix (Fin n) (Fin n) F) := rfl
    have hadj : ∀ i j, (yU : Matrix (Fin n) (Fin n) F).adjugate i j ∈ 𝒪[F] := fun i j => by
      rw [← hy₀, ← RingHom.map_adjugate]
      exact (y₀.adjugate i j).2
    have hd : ‖Ring.inverse (yU : Matrix (Fin n) (Fin n) F).det‖ ≤ 1 := by
      rw [Ring.inverse_eq_inv', norm_inv, hyv, hdet, inv_one]
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ((hO _).1 hd) (hadj i j)
  have e : t = yU * (g⁻¹ * t * g) * yU⁻¹ := by
    have e1 : cU⁻¹ * t * cU = t := by
      rw [mul_assoc, htcU, ← mul_assoc, inv_mul_cancel, one_mul]
    calc t = cU⁻¹ * t * cU := e1.symm
      _ = (cU⁻¹ * g) * (g⁻¹ * t * g) * (cU⁻¹ * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyO ht') (Subgroup.inv_mem _ hyO)

def pairGrp {G : Type} [Group G] (t N : G) (h : Commute t N) : Subgroup G where
  carrier := {x | ∃ a b : ℤ, x = t ^ a * N ^ b}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    rw [_root_.zpow_add, _root_.zpow_add, mul_assoc, mul_assoc, ← mul_assoc (N ^ b), (h.zpow_zpow c b).eq.symm, mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [_root_.mul_inv_rev, _root_.zpow_neg, _root_.zpow_neg]
    exact (h.zpow_zpow a b).inv_inv.eq.symm

theorem mem_KGL_of_commute : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ n w N t hN hsep htN htc
  set F := w.adicCompletion E
  have hNO : N ∈ integralGL F n := mem_integralGL_of_mem_KGL hN
  let H0 := pairGrp t N htN
  have hC : IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F))) :=
    htc.mul (isCompact_integralGL F n)
  have hsub : (H0 : Set (GL (Fin n) F)) ⊆
      closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) := by
    rintro _ ⟨a, b, rfl⟩
    exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers t a)) (Subgroup.zpow_mem _ hNO b)
  have hH : IsCompact (H0.topologicalClosure : Set (GL (Fin n) F)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  have ht' := hg t (H0.le_topologicalClosure ⟨1, 0, by simp⟩)
  have hN' := hg N (H0.le_topologicalClosure ⟨0, 1, by simp⟩)
  exact mem_KGL_of_mem_integralGL (mem_integralGL_of_conj N t g hNO hsep htN ht' hN')

end GlobalTheory.StabInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
section
noncomputable section

open NumberField GlobalTheory.BCT Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem mulMat_eq_map (a : B.A) :
    mulMat e b a = (e : K.E →+* w.adicCompletion E).mapMatrix (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)) := rfl

theorem mulMat_one : mulMat e b (1 : B.A) = 1 := by
  rw [mulMat_eq_map, LinearMap.mulLeft_one, LinearMap.toMatrix_id, map_one]

theorem mulMat_mul (a a' : B.A) : mulMat e b (a * a') = mulMat e b a * mulMat e b a' := by
  rw [mulMat_eq_map, mulMat_eq_map, mulMat_eq_map, LinearMap.mulLeft_mul, ← map_mul, ← LinearMap.toMatrix_mul]
  rfl

theorem mulMat_injective : Function.Injective (mulMat e b) := by
  intro a a' h
  have h1 : LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) = LinearMap.toMatrix b b (LinearMap.mulLeft K.E a') :=
    Matrix.map_injective e.injective h
  have h2 := congrArg (fun f : B.A →ₗ[K.E] B.A => f 1) ((LinearMap.toMatrix b b).injective h1)
  simpa using h2

def mulU : B.Aˣ →* GLw m w where
  toFun a := ⟨mulMat e b a, mulMat e b ((a⁻¹ : B.Aˣ) : B.A),
    by rw [← mulMat_mul, Units.mul_inv, mulMat_one], by rw [← mulMat_mul, Units.inv_mul, mulMat_one]⟩
  map_one' := Units.ext (mulMat_one e b)
  map_mul' a a' := Units.ext (mulMat_mul e b _ _)

theorem mulU_val (a : B.Aˣ) : (mulU e b a).val = mulMat e b a := rfl

theorem mulU_injective : Function.Injective (mulU e b) :=
  fun _ _ h => Units.ext (mulMat_injective e b (congrArg Units.val h))

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [CommRing K] [Algebra ℚ K]
    (x : K ⊗[ℚ] G.C) : (starT G.star K (starT G.star K x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

end GlobalTheory.FinClsLoc
end
end

