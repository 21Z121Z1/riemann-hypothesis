import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatOfTie
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.GaloisCohomology.LocalTateDualityK

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKs
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HTBasisEx

variable {l : ℕ} [Fact l.Prime]

theorem basis_of_invariants (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hE : E.1 = Ks K s) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]) (D : Submodule ↥E.1 (Fin d → P.R.BdR))
    (hD : ∀ y ∈ D, ∀ g ∈ GK E,
      ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y)
    (hfin : Module.Finite ↥E.1 ↥D) (hd : Module.finrank ↥E.1 ↥D = d) :
    ∃ (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ), LinearIndependent (PadicComplex l) e ∧
      (∀ k, ∃ y ∈ D, (∀ i, y i ∈ (P.PD E).Fil (u k)) ∧ ¬ ∀ i, y i ∈ (P.PD E).Fil (u k + 1)) ∧
      ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
        (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (e k) = e k := by
  classical
  obtain ⟨sy, hsy⟩ := GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist l P AI Θ E
  have hsum : ∀ (a : ℤ) (t : Finset (Fin d)) (f : Fin d → P.R.BdR),
      (∀ j ∈ t, f j ∈ (P.PD E).Fil a) → sy a (∑ j ∈ t, f j) = ∑ j ∈ t, sy a (f j) := by
    intro a t f
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
    | insert j t hj ih =>
      intro hf
      have ht : ∀ j ∈ t, f j ∈ (P.PD E).Fil a := fun j h => hf j (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        (hsy a).1 _ (hf j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ ht), ih ht]
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.T.exists_family_adapted_to_separated_filtration ↥E.1 (Fin d → P.R.BdR) D
    (fun a => Submodule.pi Set.univ fun _ => (P.PD E).Fil a) d hfin hd
    (fun a y hy i hi => (P.PD E).Fil_anti a (hy i hi))
    (by
      intro y
      choose n hn using fun i => (P.PD E).Fil_exh (y i)
      have hanti : Antitone (P.PD E).Fil := antitone_int_of_succ_le (P.PD E).Fil_anti
      obtain ⟨b, hb⟩ := (Set.finite_range n).bddBelow
      exact ⟨b, fun i _ => hanti (hb ⟨i, rfl⟩) (hn i)⟩)
    (fun y hy => funext fun i => (P.PD E).Fil_sep _ fun a => hy a i (Set.mem_univ i))
  have hxF : ∀ k i, x k i ∈ (P.PD E).Fil (u k) := fun k i => (hx k).2 i (Set.mem_univ i)
  have hact : ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
      (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (fun i => sy (u k) (x k i)) =
        fun i => sy (u k) (x k i) := by
    intro σ hσ k
    funext i
    have hg : ∀ j, P.actQdR σ (x k j) ∈ (P.PD E).Fil (u k) := fun j => by
      rw [← P.PD_actdR E ⟨σ, hσ⟩]
      exact (P.PD E).Fil_G _ _ _ (hxF k j)
    have h1 := congrFun (hD _ (hx k).1 σ hσ) i
    conv_rhs => rw [← h1]
    simp only [twAct, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum _ _ _ (fun j _ => by
      rw [← Algebra.smul_def]
      exact ((P.PD E).Fil (u k)).smul_of_tower_mem _ (hg j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, (hsy _).2.1 _ _ (hg j),
      (hsy _).2.2.2 σ _ (hxF k j), IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l)]
    have hc : ∀ c : Om l, (c : PadicComplex l) = algebraMap (Om l) (PadicComplex l) c :=
      fun _ => rfl
    rw [hc]
    exact mul_left_comm _ _ _
  refine ⟨fun k i => sy (u k) (x k i), u, ?_, fun k => ⟨x k, (hx k).1, hxF k, fun h => ?_⟩, hact⟩
  · refine GlobalTheory.T.serreTate_linearIndependent_of_weightwise l AI.actC P.χQ (GK E) E.1 ?_ d d _ _ u hact ?_
    · intro i y hy
      have := GlobalTheory.T.tate_invariants_cyclotomic_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs i y
        (by intro g hg; apply hy; unfold GK; rw [hE]; exact hg)
      rwa [hE]
    · intro a c hc h0
      refine hind a c hc fun i _ => ?_
      have hm : ∀ k, c k • x k i ∈ (P.PD E).Fil a := by
        intro k
        by_cases hk : u k = a
        · exact Submodule.smul_mem _ _ (hk ▸ hxF k i)
        · rw [hc k hk, zero_smul]; exact Submodule.zero_mem _
      rw [Finset.sum_apply]
      refine ((hsy a).2.2.1 _ (Submodule.sum_mem _ fun k _ => hm k)).1 ?_
      rw [hsum a _ _ fun k _ => hm k]
      have h1 := congrFun h0 i
      rw [Finset.sum_apply, Pi.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : u k = a
      · subst hk
        exact (by rw [Pi.smul_apply, Algebra.smul_def]; exact (hsy _).2.1 _ _ (hxF k i))
      · simp only [Pi.smul_apply, hc k hk, zero_smul, ZeroMemClass.coe_zero, smul_eq_mul]
        rw [((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)]
        simp
  · have := hind (u k) (Pi.single k 1) (fun j hj => Pi.single_eq_of_ne (fun e => hj (by rw [e])) _)
      (by
        intro i _
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        exact h i) k
    simp at this

set_option maxHeartbeats 1600000 in

theorem htBasis_of_isCrys (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hEs : E.1 = Ks K s) (hle : K.1 ≤ E.1) (LL : FinExt l)
    (h7K : fontCore (P.PD K)) (h7E : fontCore (P.PD E))
    (T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hcrys : IsCrys (P.PD E) (T'.ρ.comp (Subgroup.inclusion (GK_le hle))))
    {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T' M A)
    (m : ℕ) (hm : s ≤ m) :
    {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
      DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a}.Finite ∧
    HTBasis AI.actC P.χQ (Gj K m) M
      {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a} := by
  have hLL : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨bV, hbV⟩ := GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices l K LL T' d M A hM
  let ρ' : Representation ↥LL.1 ↥(GK E) T'.V := T'.ρ.comp (Subgroup.inclusion (GK_le hle))
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T'.V, ρ := T'.ρ, cont := T'.cont }
  let AE : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T'.V, ρ := ρ'
      cont := fun x => (T'.cont x).comp (continuous_inclusion (GK_le hle)) }
  have hK := h7K _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AK
  have hE := h7E _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AE
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  refine ⟨GlobalTheory.T.finite_setOf_inf_filtration_ne_succ _ _ (DdR (P.PD K) T'.ρ) (fun a => FilV (P.PD K) a) hK.2.1.1 hanti, ?_⟩
  classical
  let M0 : GQ l → Matrix (Fin d) (Fin d) ℚ_[l] := fun g =>
    if hg : g ∈ GK K then Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i else 0
  have hM0 : ∀ g (hg : g ∈ GK K), M0 g = Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i :=
    fun g hg => dif_pos hg
  have hmul : ∀ g ∈ GK K, ∀ g' ∈ GK K, M0 (g * g') = M0 g * M0 g' := by
    intro g hg g' hg'
    rw [hM0 g hg, hM0 g' hg', hM0 _ (mul_mem hg hg')]
    have key : ∀ γ : ↥(GK K), (Matrix.of fun i j => bV.repr (T'.ρ γ (bV j)) i) =
        LinearMap.toMatrix bV bV ((T'.ρ γ).restrictScalars ℚ_[l]) := fun γ => by
      ext i j
      rw [LinearMap.toMatrix_apply]; rfl
    have hcomp : (T'.ρ ⟨g * g', mul_mem hg hg'⟩).restrictScalars ℚ_[l] =
        (T'.ρ ⟨g, hg⟩).restrictScalars ℚ_[l] ∘ₗ (T'.ρ ⟨g', hg'⟩).restrictScalars ℚ_[l] := by
      refine LinearMap.ext fun v => ?_
      exact LinearMap.congr_fun (map_mul T'.ρ ⟨g, hg⟩ ⟨g', hg'⟩) v
    rw [key, key, key, hcomp]
    exact LinearMap.toMatrix_comp bV bV bV _ _
  obtain ⟨ΦE, -, hΦE⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD E) ρ' bV
  obtain ⟨DE, hDE, hfin, hdim⟩ := GlobalTheory.T.deRham_invariants_coordinates_finrank_eq (P.PD E) ρ' bV hLL hE.2.1.1 (hE.2.2 hcrys) ΦE hΦE
  have hinv : ∀ y ∈ DE, ∀ g ∈ GK E,
      ((M0 g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y := by
    intro y hy g hg
    have := (hDE y).1 hy ⟨g, hg⟩
    simp only [P.PD_actdR] at this
    rw [hM0 g (GK_le hle hg)]
    exact this
  obtain ⟨e, u, hli, hu, hact⟩ := basis_of_invariants P AI Θ K s hs E hEs M0 DE
    hinv hfin hdim
  have hFil : ∀ a x, x ∈ (P.PD E).Fil a ↔ x ∈ (P.PD K).Fil a := fun a x =>
    Set.ext_iff.1 (P.PD_Fil E K a) x
  refine ⟨e, u, hli, fun k => ?_, fun σ hσ k => ?_⟩
  · obtain ⟨y, hy, hy1, hy2⟩ := hu k
    simp only [hFil] at hy1 hy2
    obtain ⟨z, hz, hz1, hz2⟩ := GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt l P K E hle d M0 hmul (u k) y (hinv y hy) hy1 hy2
    obtain ⟨Φ, h1, h2⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro heq
    have hmem : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := by
      refine ⟨?_, (h1 _ _).2 (by simpa using hz1)⟩
      simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply Φ.injective
      rw [h2, Φ.apply_symm_apply]
      have := hz g g.2
      rw [hM0 g g.2] at this
      simp only [P.PD_actdR]
      exact this
    have hmem' : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) := by
      have heq' : DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) =
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := heq
      rw [heq']; exact hmem
    exact hz2 (by simpa using (h1 _ _).1 hmem'.2)
  · have hσE : σ ∈ GK E := by
      refine IntermediateField.fixingSubgroup_le (?_ : E.1 ≤ Ks K m) hσ
      rw [hEs]
      refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
      change x ^ (l ^ (s + n)) = 1
      rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]
    have hσK : σ ∈ GK K := GK_le hle hσE
    have hMσ : M σ = (M0 σ).map (algebraMap ℚ_[l] (PadicComplex l)) := by
      rw [hM0 σ hσK]
      ext i j
      exact hbV ⟨σ, hσK⟩ i j
    have := hact σ hσE k
    unfold twAct at this ⊢
    rw [hMσ]
    exact this

theorem exists_htBasis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  intro D HW F h7 l _ K s LL h S E' T hcr d M A hM m hm
  obtain ⟨Θ⟩ := GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData D l
  obtain ⟨E, hEs⟩ : ∃ E : FinExt l, E.1 = Ks K s :=
    ⟨⟨Ks K s, GlobalTheory.MemLoc.finiteDimensional_Ks_of_finExt K s⟩, rfl⟩
  have hle : K.1 ≤ E.1 := hEs ▸ h.2.2.1
  exact htBasis_of_isCrys (D.loc l) (D.locA l) Θ K s ⟨h.1, h.2.1⟩ E hEs hle LL (h7 l K) (h7 l E) T
    (GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h) E hEs hle T hcr)
    M A hM m hm

end GlobalTheory.HTBasisEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeOfPowMem
section
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.EtaleExact TensorProduct

namespace GlobalTheory.EtaleSub

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

include E in

theorem surjective_of_tie (hfl : Module.Flat O RW) {T' T : LocLat G Qp LL O}
    (hfix : ∀ b, TWmap φR T' b = b → ∃ t : ↥T'.L.T, b = (1 : RW) ⊗ₜ[O] t)
    (hone : Function.Injective fun t : ↥T.L.T => (1 : RW) ⊗ₜ[O] t)
    (ι : LatHom T'.L T.L) (hι : Function.Injective ι.f) (m : ℕ) (hm : (m : LL) ≠ 0)
    (hall : ∀ x : W.DD T, ((m : ℕ) : W.EE) • x ∈ LinearMap.range (W.map ι)) :
    Function.Surjective ι.f := by
  have hU := span_range_map E ι
  have hkill : ∀ y : TW RW T, m • y ∈ LinearMap.range ((latMap ι).baseChange RW) := by
    intro y
    have hy : y ∈ Submodule.span RW (Set.range (E.jD T)) := by
      rw [E.jD_span T]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← hU]
      refine Submodule.subset_span ⟨_, hall x, ?_⟩
      rw [E.jD_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    | zero => simp
    | add z w _ _ hz hw => rw [smul_add]; exact Submodule.add_mem _ hz hw
    | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
  have hinj : Function.Injective ((latMap ι).baseChange RW) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := RW) (latMap ι)
      (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
  have hcomm : ∀ c : TW RW T', (latMap ι).baseChange RW (TWmap φR T' c) =
      TWmap φR T ((latMap ι).baseChange RW c) := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul r t => simp [TWmap]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ t : ↥T.L.T, ∃ t' : ↥T'.L.T, latMap ι t' = m • t := by
    intro t
    obtain ⟨c, hc⟩ := hkill ((1 : RW) ⊗ₜ[O] t)
    rw [← TensorProduct.tmul_smul] at hc
    have hf : TWmap φR T' c = c := by
      apply hinj
      rw [hcomm, hc]
      simp [TWmap]
    obtain ⟨t', rfl⟩ := hfix c hf
    refine ⟨t', hone ?_⟩
    simpa using hc
  have hle : (T.L.T : Set T.V) ⊆ (LinearMap.range ι.f : Submodule LL T.V) := by
    intro t ht
    obtain ⟨t', h'⟩ := h2 ⟨t, ht⟩
    refine ⟨(m : LL)⁻¹ • (t' : T'.V), ?_⟩
    have h3 : ι.f (t' : T'.V) = m • t := congrArg Subtype.val h'
    rw [map_smul, h3, ← Nat.cast_smul_eq_nsmul LL, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have htop : LinearMap.range ι.f = ⊤ :=
    top_le_iff.1 (T.L.span ▸ Submodule.span_le.2 hle)
  exact LinearMap.range_eq_top.1 htop

end Generic

theorem exists_lattice_of_pow_mem : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.LitSub D HW F := by
  intro D HW F l _ K LL hA T D' hpow hφ hγ
  obtain ⟨T', ι, hι, hr⟩ := exists_sublattice (D.locA l) (HW l) (F l) K 1 LL hA.2.2 T D' hφ hγ
  obtain ⟨a, ha⟩ := hpow
  refine ⟨T', ι, ⟨hι, ?_⟩, hr⟩
  haveI := flat_RW LL
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  have hp : (((D.loc l).PD K).p : ℕ) = l := (D.loc l).PD_p K
  refine surjective_of_tie ((F l).E K 1 LL hA.2.2).tie (flat_RW LL)
    (fun b hb => ((GlobalTheory.WittTensorFixed.main l K LL T').2.1 b).1 hb)
    (GlobalTheory.WittTensorFixed.main l K LL T).2.2 ι hι (l ^ a) ?_ ?_
  · exact_mod_cast pow_ne_zero a (Fact.out : l.Prime).ne_zero
  · intro x
    rw [hr]
    have := ha x
    rw [hp] at this
    simpa using this

end GlobalTheory.EtaleSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalars
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem intertwine_mul {G ι R S : Type} [Monoid G] [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (B : G → Matrix ι ι S) (hB1 : B 1 = 1)
    (hBm : ∀ g h, B (g * h) = B g * B h) (p : GL ι S) (T : G → Matrix ι ι R)
    (hT : ∀ g, (p : Matrix ι ι S) * (T g).map f = B g * p) :
    T 1 = 1 ∧ ∀ g h, T (g * h) = T g * T h := by
  have hinj : Function.Injective (fun M : Matrix ι ι R => M.map f) := Matrix.map_injective hf
  refine ⟨?_, fun g h => ?_⟩
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T 1).map f = (p : Matrix ι ι S) * (1 : Matrix ι ι R).map f
    rw [hT, hB1, one_mul, Matrix.map_one f (map_zero f) (map_one f), mul_one]
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T (g * h)).map f = (p : Matrix ι ι S) * (T g * T h).map f
    calc (p : Matrix ι ι S) * (T (g * h)).map f = B g * B h * p := by rw [hT, hBm]
      _ = B g * ((p : Matrix ι ι S) * (T h).map f) := by rw [mul_assoc, hT]
      _ = ((p : Matrix ι ι S) * (T g).map f) * (T h).map f := by rw [← mul_assoc, hT]
      _ = (p : Matrix ι ι S) * (T g * T h).map f := by rw [Matrix.map_mul, mul_assoc]

theorem exists_ratForm : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  intro l _ n _ _ K r σ ω W hσ hW hω hcoef
  classical

  let P0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  let Q0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) ((W⁻¹ : GL (Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  have hPQ : P0 * Q0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  have hQP : Q0 * P0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  let p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ⟨P0, Q0, hPQ, hQP⟩
  have hp : ∀ i m j k, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) (i, m) (j, k) =
      if i = j then (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k else 0 := by
    intro i m j k
    show P0 (i, m) (j, k) = _
    simp only [P0, Matrix.kronecker_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hA : ∀ (i j : n) (k : Fin r), ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
      fr l m ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) =
        ∑ k', (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k' * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k') := by
    intro i j k
    refine hcoef ↥(GK K) (fun g => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) (fun g => ?_) ?_
    · rw [map_mul, hσ.rat, hω]
    · show Continuous fun g => (((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) * ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l)
      exact (hσ.cont i j).mul continuous_const
  choose A hAc hA using hA
  let T : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g x y => A x.1 y.1 y.2 g x.2
  let B : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have hB1 : B 1 = 1 := by
    simp only [B, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.blockDiagonal_one
  have hBm : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, map_mul, Units.val_mul, Matrix.map_mul]
    rw [Matrix.blockDiagonal_mul]
  have hT : ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (T g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
      B g * p := by
    intro g
    refine Matrix.ext ?_
    rintro ⟨i, m⟩ ⟨j, k⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hp, B, T, Matrix.map_apply, Matrix.blockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    refine (show _ = ∑ x, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m x * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (A i j k g x)
      from rfl).trans ?_
    rw [← hA i j k g m, map_mul]
    symm
    simp [hW]
  obtain ⟨hT1, hTm⟩ := intertwine_mul (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
    B hB1 hBm p T hT
  let T' : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := T, map_one' := hT1, map_mul' := hTm }
  refine ⟨T'.toHomUnits, p, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, k'⟩ ⟨j, k⟩
    exact (continuous_apply k').comp (hAc i j k)
  · rintro ⟨i, m⟩ ⟨j, k⟩
    apply hσ.le
    rw [hp]
    split_ifs
    · rw [hW]; exact fr_comm (hω k) m
    · exact map_zero _
  · intro g
    exact hT g
  · intro c hc hcc
    have hC : ∀ i : n, ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
        fr l m (c g i) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k) :=
      fun i => hcoef ↥(GK K) (fun g => c g i) (fun g => hc g i) (hcc i)
    choose a hac ha using hC
    refine ⟨fun g x => a x.1 g x.2, continuous_pi fun x => (continuous_apply x.2).comp (hac x.1), fun g => ?_⟩
    funext ⟨i, m⟩
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp only [hp, ite_mul, zero_mul]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    rw [ha i g m]

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_block_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  first | exact @GlobalTheory.PMon.extPeriodMatrix | exact GlobalTheory.PMon.extPeriodMatrix | (intros; apply GlobalTheory.PMon.extPeriodMatrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_Dst_of_isSst' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  first | exact @GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | exact GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | (intros; apply GlobalTheory.Pst.finiteDimensional_Dst_of_isSst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), TateFiniteness (P.PD K) := by
  first | exact @GlobalTheory.TateFiniteH1.tate_finH1 | exact GlobalTheory.TateFiniteH1.tate_finH1 | (intros; apply GlobalTheory.TateFiniteH1.tate_finH1 <;> assumption)
end

