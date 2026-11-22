import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumns
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonCob

theorem coboundary_cols (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P) :
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  intro h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] (ι → Bst P) :=
    TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : ι → ℚ_[l]) (a : Bst P) (x : ι) => v x • a)
      (fun v w a => by funext x; simp [add_smul])
      (fun c v a => by funext x; simp [mul_smul])
      (fun v a a' => by funext x; simp [smul_add])
      (fun c v a => by funext x; simp [smul_comm c]))
  have hΦ : ∀ (v : ι → ℚ_[l]) (a : Bst P), Φ (v ⊗ₜ a) = fun x => v x • a := fun v a => by
    simp [Φ]
  have hst : ∀ (g : ↥(GK K)) (y : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
      Φ (stRep P (repOf ρ₀) g y) = ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (Φ y x)) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => funext x; simp [Matrix.mulVec, dotProduct]
    | tmul v a =>
      rw [stRep_tmul, repOf_apply, hΦ, hΦ]
      funext x
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
    | add y z hy hz =>
      rw [map_add, map_add, hy, hz, ← Matrix.mulVec_add]
      congr 1
      funext x
      simp
  refine ⟨Φ b, fun g => ?_⟩
  have := congrArg Φ (h g)
  rw [map_sub, hst, hΦ] at this
  rw [← this]
  funext x
  simp [Algebra.algebraMap_eq_smul_one]

end GlobalTheory.PMonCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRham
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CobColumn

theorem coboundary_tmul_of_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  intro l _ P K ι _ _ ρ₀ c₀ β h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (ι → P.R.BdR) :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).toLinearMap ∘ₗ (TensorProduct.comm ℚ_[l] _ _).toLinearMap
  have hΦinj : Function.Injective Φ :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).injective.comp (TensorProduct.comm ℚ_[l] _ _).injective
  have hΦ : ∀ v b i, Φ (v ⊗ₜ b) i = algebraMap ℚ_[l] P.R.BdR (v i) * b := by
    intro v b i
    simp [Φ, piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]
  have hact : ∀ g v b, actVdR (P.PD K) (repOf ρ₀) g (v ⊗ₜ b) = repOf ρ₀ g v ⊗ₜ P.actQdR (g : GQ l) b := by
    intro g v b
    rw [← P.PD_actdR K g b]
    rfl
  refine ⟨∑ x, Pi.single x 1 ⊗ₜ β x, fun g => hΦinj ?_⟩
  funext i
  have hi := congrFun (h g) i
  simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hact, hΦ, repOf_apply, mul_one]
  rw [hi]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    rw [Finset.sum_eq_single x (fun y _ hy => by simp [Pi.single_eq_of_ne hy]) (by simp)]
    simp
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne' hx]
    · simp

end GlobalTheory.CobColumn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrthV

theorem exists_unitLattice {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
      L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  have hχ : ∀ g, ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
    intro g
    refine Formalism.MainNotions.BlochKatoDuality.Br.zl_int hO _ ?_
    rw [P.PD_χ K g]
    obtain ⟨a, ha, _⟩ := P.χQ_cyc (g : GQ l) 0 1 (one_pow _)
    have h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by
      ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := hχ g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

theorem cocycle_mem_coboundaries_of_tate_orthogonal' : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm b hb horth
  obtain ⟨⟨hDom, hDVR, hFrac⟩, hfd, hmt, htr, hopen⟩ := id hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := htr
  haveI : IsTopologicalAddGroup A'.V := IsModuleTopology.topologicalAddGroup LL A'.V
  obtain ⟨L1, hL1⟩ := exists_unitLattice P K LL O hO
  obtain ⟨LA, LA', hLL', -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hT'open : IsOpen (LA'.T : Set A'.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA'.T LA'.fg LA'.span
  have hL1open : IsOpen (L1.T : Set LL) := by
    rw [hL1]
    have e : ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) =
        Set.range (algebraMap O LL) := by
      ext y; simp [Algebra.linearMap_apply]
    rw [e]; exact hopen
  have hp : ((l : ℕ) : LL) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

  have hcobZ : ∀ x : A'.V, (fun g => A'.ρ g x - x) ∈ continuousCocycles A'.ρ := by
    intro x
    refine ⟨(A'.cont x).sub continuous_const, fun g h => ?_⟩
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

  have key : ∀ n : ℕ, ∃ β ∈ latticeCocycles LA', b - ((l : LL) ^ n) • β ∈ B1 A'.ρ := by
    intro n
    set s : LL := (((l : ℕ) : LL) ^ n)⁻¹ with hs
    let c : ↥(GK K) → A'.V ⧸ LA'.T := fun g => Submodule.Quotient.mk (s • b g)
    have hcZ : c ∈ divisibleCocycles LA' := by
      refine ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA'.T hT'open _ (hb.1.const_smul s), fun g h => ?_⟩
      show Submodule.Quotient.mk (s • b (g * h)) = Submodule.Quotient.mk (s • b g) +
        actD LA' g (Submodule.Quotient.mk (s • b h))
      rw [hb.2 g h, smul_add, Submodule.Quotient.mk_add]
      congr 1
      show _ = Submodule.Quotient.mk (A'.ρ g (s • b h))
      rw [map_smul]
    have hcorth : ∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c) := by
      intro d hd
      obtain ⟨f, hfc, hf⟩ := horth d hd.1
      refine ⟨fun g => (Submodule.Quotient.mk (s • f g) : LL ⧸ L1.T),
        ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hL1open _ (hfc.const_smul s), fun _ => Submodule.mem_top⟩, ?_⟩
      funext x
      obtain ⟨g, h⟩ := x
      have hf' : ((cycLL (P.PD K) LL g : LLˣ) : LL) • f h - f (g * h) + f g =
          m (d g) (A'.ρ g (b h)) := congrFun hf (g, h)
      have hlift : liftD LA' (c h) - s • b h ∈ LA'.T :=
        (Submodule.Quotient.eq _).1 (Submodule.Quotient.mk_surjective LA'.T (c h)).choose_spec
      obtain ⟨e, he⟩ := (hLL'.2 _).1 (LA'.stable g _ hlift) (d g) (hd.2 g (Set.mem_univ g))
      show (Submodule.Quotient.mk (((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h)) : LL ⧸ L1.T) -
          Submodule.Quotient.mk (s • f (g * h)) + Submodule.Quotient.mk (s • f g) =
          Submodule.Quotient.mk (m (d g) (A'.ρ g (liftD LA' (c h))))
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hL1]
      have e1 : ((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h) - s • f (g * h) + s • f g =
          s • m (d g) (A'.ρ g (b h)) := by
        rw [← hf']; simp only [smul_eq_mul]; ring
      have e2 : m (d g) (A'.ρ g (liftD LA' (c h))) =
          s • m (d g) (A'.ρ g (b h)) + m (d g) (A'.ρ g (liftD LA' (c h) - s • b h)) := by
        simp only [map_sub, map_smul, add_sub_cancel]
      rw [e1, e2]
      refine ⟨-e, ?_⟩
      show algebraMap O LL (-e) = _
      rw [map_neg, ← he]
      abel
    obtain ⟨xbar, hx⟩ := GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m
      hLL' c hcZ hcorth
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective LA'.T xbar
    refine ⟨fun g => s • b g - (A'.ρ g x - x), ⟨(continuousCocycles A'.ρ).sub_mem ((continuousCocycles A'.ρ).smul_mem s hb) (hcobZ x),
      fun g _ => ?_⟩, ?_⟩
    · have hg : Submodule.Quotient.mk (A'.ρ g x) - Submodule.Quotient.mk x =
          (Submodule.Quotient.mk (s • b g) : A'.V ⧸ LA'.T) := congrFun hx g
      rw [← Submodule.Quotient.mk_sub] at hg
      exact (Submodule.Quotient.eq _).1 hg.symm
    · refine ⟨(((l : ℕ) : LL) ^ n) • x, ?_⟩
      funext g
      have hps : (((l : ℕ) : LL) ^ n) * s = 1 := mul_inv_cancel₀ (pow_ne_zero n hp)
      simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul,
        Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul, hps, one_smul]
      abel

  have hl : ((l : ℕ) : O) ∉ nonunits O → False := by
    intro hu
    have hu' : IsUnit ((l : ℕ) : O) := by simpa [mem_nonunits_iff] using hu
    have hc := (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO).2.2.2
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu'
    have h10 : (1 : O) = 0 := by
      apply hc.toIsHausdorff.haus 1
      intro n
      rw [htop, Ideal.top_pow, Submodule.top_smul]
      exact SModEq.top
    exact one_ne_zero h10
  have hne : Ideal.span {((l : ℕ) : O)} ≠ ⊤ := by
    intro htop
    apply hl
    intro hmem
    exact hmem (Ideal.span_singleton_eq_top.1 htop)
  haveI hfinH : Module.Finite O (LatticeCohomology LA') :=
    GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  let S : Submodule O ↥(latticeCocycles LA') := ((B1 A'.ρ).restrictScalars O).comap (latticeCocycles LA').subtype
  have hBS : (latticeCoboundaries LA').comap (latticeCocycles LA').subtype ≤ S := by
    rintro z ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  haveI : Module.Finite O (↥(latticeCocycles LA') ⧸ S) := by
    refine Module.Finite.of_surjective (Submodule.factor hBS) ?_
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥(latticeCocycles LA') ⧸ S) _ hne
  obtain ⟨β0, hβ0, hbβ0⟩ := key 0
  rw [pow_zero, one_smul] at hbβ0
  have hq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) = 0 := by
    rw [← Submodule.mem_bot O, ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨β, hβ, hbβ⟩ := key i
    have heq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) =
        (((l : ℕ) : O) ^ i) • Submodule.Quotient.mk ⟨β, hβ⟩ := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show β0 - (((l : ℕ) : O) ^ i) • β ∈ B1 A'.ρ
      have h1 : β0 - (((l : ℕ) : O) ^ i) • β = (b - ((l : LL) ^ i) • β) - (b - β0) := by
        rw [← algebraMap_smul LL (((l : ℕ) : O) ^ i) β, map_pow, map_natCast]
        abel
      rw [h1]
      exact (B1 A'.ρ).sub_mem hbβ hbβ0
    rw [heq, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hβ0B : β0 ∈ B1 A'.ρ := (Submodule.Quotient.mk_eq_zero S).1 hq
  have : b = (b - β0) + β0 := by abel
  rw [this]
  exact (B1 A'.ρ).add_mem hbβ0 hβ0B

end GlobalTheory.TateOrthV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.cocycle_rat_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  intro l _ n _ _ K r σ ρ₀ p c c₀ hint hc0 hc g h
  set f : ℚ_[l] →+* ↥(MaximalUnramifiedExtension l) := algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) with hf
  set P : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hP

  have hC : (fun x : n × Fin r => fr l x.2 (c (g * h) x.1)) =
      (fun x : n × Fin r => fr l x.2 (c g x.1)) +
        (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).mulVec
          (fun x : n × Fin r => fr l x.2 (c h x.1)) := by
    funext ⟨i, m⟩
    simp only [hc, Pi.add_apply, map_add, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.blockDiagonal_apply, Matrix.map_apply, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have key : P.mulVec (fun x => f (c₀ (g * h) x)) =
      P.mulVec (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    rw [hc0, hC, ← hc0 g, ← hc0 h, Matrix.mulVec_mulVec, ← hint g]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    congr 1
    funext x
    simp only [Pi.add_apply, map_add]
    congr 1
    rw [RingHom.map_mulVec]
    rfl
  have inj : (fun x => f (c₀ (g * h) x)) =
      (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    have := congrArg (fun v => ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec v) key
    simp only [hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this
  funext x
  exact f.injective (congrFun inj x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffMemOfToLamMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.LowCoeff

def genChar {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] (u : ι → T) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* T where
  toFun g := ∏ q, u q ^ (g.toAdd q).val
  map_one' := by simp
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]

open Classical in
theorem genChar_single {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] [Fact (1 < n)] (u : ι → T)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : genChar n u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem coeff_mem_of_toLam_mem : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (I : Ideal (X.O0 i)), 0 < nu X i → nu X i + 1 ≤ M → (X.l i : X.O0 i) ^ (nu X i + 1) ∈ I → ∀ F : MvPolynomial ι (X.O0 i), toLam X i M ι F ∈ I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) → ∀ m : ι →₀ ℕ, m.degree < X.l i ^ (M - nu X i - 1) → F.coeff m ∈ I := by
  intro D N X i M ι _ I _ hM h4 F hF m hm
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  let J : Ideal (MvPolynomial ι (X.O0 i)) :=
    I.map (MvPolynomial.C : X.O0 i →+* MvPolynomial ι (X.O0 i)) ⊔ MvPolynomial.idealOfVars ι (X.O0 i) ^ (X.l i ^ (M - nu X i - 1))
  let π : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] (MvPolynomial ι (X.O0 i) ⧸ J) := Ideal.Quotient.mkₐ (X.O0 i) J
  have hI : ∀ a ∈ I, algebraMap (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) a = 0 := by
    intro a ha
    rw [← π.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  have h4' : ((X.l i : ℕ) : MvPolynomial ι (X.O0 i) ⧸ J) ^ (nu X i + 1) = 0 := by
    have := hI _ h4
    rwa [map_pow, map_natCast] at this
  have h1 : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : Fact (1 < X.l i ^ M) := ⟨h1⟩
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + π (MvPolynomial.X q)) ^ (X.l i ^ M) = 1 := by
    intro q
    refine KStar.Tree.one_add_pow_prime_pow_eq_one hp h4' hM ?_
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_right (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self q)) _))
  let L := MonoidAlgebra.lift (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) (Del X i M ι)
    (genChar (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu)
  have hc : L.comp (toLam X i M ι) = π := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, MonoidAlgebra.lift_of]
    have := genChar_single (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu q
    rw [sub_eq_iff_eq_add']
    convert this
  have hker : I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ RingHom.ker L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, L.commutes]
    exact hI a ha
  have hFJ : F ∈ J := by
    have h0 : L (toLam X i M ι F) = 0 := hker hF
    have : π F = 0 := by rw [← hc]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hFJ
  have hb0 : b.coeff m = 0 := (MvPolynomial.mem_pow_idealOfVars_iff' _ b).1 hb m hm
  rw [MvPolynomial.coeff_add, hb0, add_zero]
  exact MvPolynomial.mem_map_C_iff.1 ha m

end GlobalTheory.StepTwo.LowCoeff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.CMType

theorem isCMType_conj {E : Type} [Field E] {I : Type} (φ : I → E →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    IsCMType fun i => ComplexEmbedding.conjugate (φ i) := by
  unfold IsCMType
  intro σ
  have hmk : ∀ j, InfinitePlace.mk (φ j) = InfinitePlace.mk σ ↔
      (σ = ComplexEmbedding.conjugate (φ j) ∨
        σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j))) := by
    intro j
    have cc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)) = φ j := star_star (φ j)
    rw [InfinitePlace.mk_eq_iff, cc]
    constructor
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
  obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk σ)
  exact ⟨i, (hmk i).1 hi, fun j hj => h.1 (((hmk j).2 hj).trans hi.symm)⟩

theorem phi_cmType : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R),
    IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  intro R H
  obtain ⟨_, -, ⟨-, -, -, -, hbij⟩, -, hsq, -⟩ := GlobalTheory.Mem.HostCM.host_cm_embedding_properties R H
  refine ⟨isCMType_conj (embPsi H) hbij, fun g g' => ?_⟩
  show ComplexEmbedding.conjugate (embPsi H g) H.sqrtMinusD =
    ComplexEmbedding.conjugate (embPsi H g') H.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hsq g, hsq g']

end GlobalTheory.LamTie.CMType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportVal
section
noncomputable section

namespace GlobalTheory.Pass.CutEq

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem main : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i),
    PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  intro D i Xs π
  have h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π := by
    unfold ccAt GlobalTheory.Cut.ccOff Ideal.map
    congr 1
    ext a
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩
      have := congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩
      exact this
    · rintro ⟨f, hf, h0, rfl⟩
      refine ⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩
      have hy := y.2
      simp only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy
      exact h0 y.1 hy.2 hy.1
  unfold vccCut GlobalTheory.Cut.vccOff
  rw [h]

end GlobalTheory.Pass.CutEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAlgHomSubDvdOfXDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_subgroup_filtration_index_bounded : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (γ : GQ l) (k : ℕ), 2 ≤ k → ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∃ H : ℕ → Subgroup (GQ l), (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧ (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧ (∀ n, γ ^ l ^ n ∈ H n) ∧ ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) := by
  first | exact @GlobalTheory.galois_congruence_chain | exact GlobalTheory.galois_congruence_chain | (intros; apply GlobalTheory.galois_congruence_chain <;> assumption)
end

