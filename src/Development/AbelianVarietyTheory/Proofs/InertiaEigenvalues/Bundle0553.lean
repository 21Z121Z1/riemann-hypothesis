import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0228
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.StepGlobalPf

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chi_one_eq_one (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨e, he⟩ := hD
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  have h1 : mapM (toK D.nd i) (rO D.nd i r π) γ = 1 := by
    simp [mapM, rO, hγ]
  simp only [h1, Matrix.one_mulVec, hu, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

theorem noChiOff (Xs : Set (D.nd.X i)) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : GlobalTheory.Cut.NoChiOff i r Xs := by
  intro x _ hxZ u hu
  by_contra hu0
  refine hxZ (hG6 x ⟨u, hu0, fun g => ?_⟩)
  have h := hu g
  rw [rTwO, mapM_twistM, Matrix.smul_mulVec] at h
  conv_rhs => rw [← h]
  rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
    one_smul]

theorem unrOut (Xs : Set (D.nd.X i)) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    GlobalTheory.Cut.UnrOut i r Xs := by
  intro v hvl hvS hvQ x _ γ hγ
  have hχ := chi_one_eq_one i r ρ π hD (hG4 π v hvl hvS hvQ γ hγ)
  have hx : rO D.nd i r x γ = 1 := by simp [rO, hG4 x v hvl hvS hvQ γ hγ]
  rw [rTwO, twistM]
  simp [hx, hχ]

theorem atS (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.S i, (GlobalTheory.Cut.QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ GlobalTheory.Cut.PolyAt i r Xs π v := by
  intro v hv
  have hS := ((D.nd.S_def i v).1 hv).1
  have hv5 := hG5 v (Or.inl hv)
  have hv5x := hG5x v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hv5.2 hk hv hv5x.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hv5.1 (Or.inr hp)) x).1 γ hγ, hv5x.2.2.2 hv hp⟩

theorem atQ (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.Q i, GlobalTheory.Cut.QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1 := fun v hv =>
  ⟨fun x _ γ hγ => ((hG5 v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ, (hG5x v (Or.inr hv)).2.2.1 hv⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → StepGlobal := by
  intro hA D i r ρ π Xs eρ eχ hr _ _ hG4 hG5 hG5x hG6 hDec _ _ hS hZ hπ hl hsel hsha
  obtain ⟨S, hS⟩ := hS
  rw [GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal]
  exact GlobalTheory.CutCore.main hA D i r ρ π Xs eρ eχ S hr hS hZ hπ (noChiOff i r Xs hG6) (unrOut i r ρ π Xs hG4 hDec)
    (atS i r π Xs hG5 hG5x) (atQ i r Xs hG5 hG5x)
    (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eρ).1 (hl w hw).2.1,
      fun c hc => (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eχ).1 ((hl w hw).2.2 c hc)⟩) hsel hsha

end GlobalTheory.StepGlobalPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDualStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_reduction_index_bound_of_tateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  first | exact @GlobalTheory.BoundedIndex.h1_reduction_index_bounded | exact GlobalTheory.BoundedIndex.h1_reduction_index_bounded | (intros; apply GlobalTheory.BoundedIndex.h1_reduction_index_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLqPerm

theorem isChar_one {G : Type} [Group G] : IsChar (fun _ : G => (1 : ℂ)) := by
  refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), fun x => ?_⟩
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) x) = 1
  simp [Representation.trivial, LinearMap.trace_id]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

variable {g : ℕ} [Fact g.Prime]

theorem isChar_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) := by
  induction L with
  | nil => exact isChar_one
  | cons p L ih =>
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    exact ((GlobalTheory.T.harishChandra_induction_character_restriction_decomp g p.1 (degL L) (degL (p :: L)) hdeg).1 p.2 (hcL L (degL L))
      (hL p (by simp)) (ih fun q hq => hL q (by simp [hq])))

theorem degL_perm {L L' : List (Pc g)} (h : L.Perm L') : degL L = degL L' := by
  unfold degL
  exact (h.map _).sum_eq

theorem hc_congr_mid (a : ℕ) (α : Gn g a → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc a m α (F m) n = hc a m' α (F m') n := by subst h; rfl

theorem hc_congr_left (c : ℕ) (γ : Gn g c → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc m c (F m) γ n = hc m' c (F m') γ n := by subst h; rfl

theorem hcL_perm {L L' : List (Pc g)} (h : L.Perm L') :
    (∀ p ∈ L, IsChar p.2) → ∀ n, n = degL L → hcL L n = hcL L' n := by
  induction h with
  | nil => intro _ n _; rfl
  | cons x h ih =>
    rename_i L₁ L₂
    intro hc1 n hn
    rw [hcL_cons, hcL_cons, ih (fun q hq => hc1 q (by simp [hq])) _ rfl]
    exact hc_congr_mid x.1 x.2 (hcL L₂) n _ _ (degL_perm h)
  | swap x y L₁ =>
    intro hc1 n hn
    have hx : IsClass x.2 := isClass_of_isChar (hc1 x (by simp))
    have hy : IsClass y.2 := isClass_of_isChar (hc1 y (by simp))
    have hL : IsClass (hcL L₁ (degL L₁)) :=
      isClass_of_isChar (isChar_hcL L₁ fun q hq => hc1 q (by simp [hq]))
    have hn' : n = y.1 + x.1 + degL L₁ := by rw [hn]; simp [degL]; omega
    have hn'' : n = x.1 + y.1 + degL L₁ := by rw [hn']; omega
    have e1 : degL (x :: L₁) = x.1 + degL L₁ := by simp [degL]
    have e2 : degL (y :: L₁) = y.1 + degL L₁ := by simp [degL]
    simp only [hcL_cons]
    rw [hc_congr_mid y.1 y.2 (fun m => hc x.1 (degL L₁) x.2 (hcL L₁ (degL L₁)) m) n _ _ e1,
      hc_congr_mid x.1 x.2 (fun m => hc y.1 (degL L₁) y.2 (hcL L₁ (degL L₁)) m) n _ _ e2]
    rw [← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) n y.2 x.2 _ hy hx hL).1 hn',
      ← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g x.1 y.1 (degL L₁) n x.2 y.2 _ hx hy hL).1 hn'',
      (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) (y.1 + x.1) y.2 x.2 _ hy hx hL).2.1 rfl]
    exact hc_congr_left (degL L₁) (hcL L₁ (degL L₁)) (fun m => hc x.1 y.1 x.2 y.2 m) n _ _ (Nat.add_comm _ _)
  | trans h₁ h₂ ih₁ ih₂ =>
    intro hc1 n hn
    rw [ih₁ hc1 n hn, ih₂ (fun q hq => hc1 q (h₁.mem_iff.mpr hq)) n (hn.trans (degL_perm h₁))]

end GlobalTheory.GLqPerm

theorem GlobalTheory.gl_list_product_perm_char : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  intro g _ L L' n hn hL
  subst hn
  exact ⟨GlobalTheory.GLqPerm.isChar_hcL L hL, fun h => GlobalTheory.GLqPerm.hcL_perm h hL _ rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZero
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem list_sum_posNat {ι : Type} (L : List ι) (f : ι → ℂ) (hf : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ f p = n) :
    ∃ m : ℕ, (L.map f).sum = m ∧ (L ≠ [] → 0 < m) := by
  induction L with
  | nil => exact ⟨0, by simp, fun h => absurd rfl h⟩
  | cons p L ih =>
    obtain ⟨n, hn, hp⟩ := hf p (List.mem_cons_self ..)
    obtain ⟨m, hm, -⟩ := ih fun q hq => hf q (List.mem_cons_of_mem _ hq)
    refine ⟨n + m, ?_, fun _ => by omega⟩
    simp [List.map_cons, List.sum_cons, hp, hm]

theorem res_cusp_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d →
    ∀ x y, res a (d - a) χ x y = 0 := by
  intro g _ d a χ hχ ha had x y
  obtain ⟨-, hirr, hc⟩ := hχ
  have hchar : IsChar χ := by
    obtain ⟨V, -, hV⟩ := hirr
    exact ⟨V, hV⟩
  obtain ⟨L, hL, hres⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a (d - a) d (by omega)).2 χ hchar
  have hpos : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ (fun p : (Gn g a → ℂ) × (Gn g (d - a) → ℂ) => p.1 1 * p.2 1) p = n := by
    intro p hp
    obtain ⟨d₁, hd₁, h₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g a) 0 p.1).2.1 (hL p hp).1
    obtain ⟨d₂, hd₂, h₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g (d - a)) 0 p.2).2.1 (hL p hp).2
    exact ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, by simp [h₁, h₂]⟩
  obtain ⟨m, hm, hmpos⟩ := list_sum_posNat L _ hpos
  have hL0 : L = [] := by
    by_contra hne
    have h0 : res a (d - a) χ 1 1 = 0 := hc a ha had
    rw [hres, hm] at h0
    have := hmpos hne
    exact absurd (by exact_mod_cast h0 : m = 0) (by omega)
  rw [hres, hL0]
  simp

end GlobalTheory.GLq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegree
section
noncomputable section

namespace GlobalTheory.JSW

theorem tsum_fibre_entrySum_eq {m : ℕ} {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (F : (Fin m → ℕ) → E) (d : ℕ) :
    ∑' b : (fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}, F b.1.1 =
      ∑ l ∈ antiParts m d, F l := by
  rw [← Finset.tsum_subtype (antiParts m d) F]
  let e : ((fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}) ≃
      {x // x ∈ antiParts m d} :=
    { toFun := fun b => ⟨b.1.1, mem_antiParts.2 ⟨b.2, b.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_antiParts.1 x.2).2⟩, (mem_antiParts.1 x.2).1⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  exact e.tsum_eq (fun x => F x.1)

theorem regroup_antiParts {m : ℕ} (G : (Fin m → ℕ) → ℂ)
    (hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) :
    Summable (fun d => ‖∑ l ∈ antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  set σ : {l : Fin m → ℕ // Antitone l} → ℕ := fun l => ∑ i, l.1 i with hσ
  have h1 := hG.hasSum.tsum_fiberwise σ
  have h1' : Summable (fun d => ∑ l ∈ antiParts m d, ‖G l‖) := by
    refine h1.summable.congr fun d => ?_
    exact tsum_fibre_entrySum_eq (fun l => ‖G l‖) d
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sum_le _ _) h1', ?_⟩
  intro s hs
  have hg : Summable fun l : {l : Fin m → ℕ // Antitone l} => G l.1 := hG.of_norm
  have h2 := hg.hasSum.tsum_fiberwise σ
  have h2' : HasSum (fun d => ∑ l ∈ antiParts m d, G l) (∑' l : {l : Fin m → ℕ // Antitone l}, G l.1) :=
    h2.congr_fun fun d => (tsum_fibre_entrySum_eq G d).symm
  rw [hs.unique h2']
  exact hg.hasSum

example : ∀ {m : ℕ} (G : (Fin m → ℕ) → ℂ),
    (Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) →
    Summable (fun d => ‖∑ l ∈ GlobalTheory.JSW.antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ GlobalTheory.JSW.antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s :=
  fun G hG => regroup_antiParts G hG

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValuesStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herr_class_of_cocycle_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  first | exact @GlobalTheory.NL.HerrClassUniq.class_of_values | exact GlobalTheory.NL.HerrClassUniq.class_of_values | (intros; apply GlobalTheory.NL.HerrClassUniq.class_of_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelationsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herr_cocycle_of_witt_tensor_relations : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  first | exact @GlobalTheory.NL.HerrCocycleCriterion.cocyc | exact GlobalTheory.NL.HerrCocycleCriterion.cocyc | (intros; apply GlobalTheory.NL.HerrCocycleCriterion.cocyc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamilyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_basis_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  first | (exact @GlobalTheory.HodgeAt.hodge_of_adapted) | (exact GlobalTheory.HodgeAt.hodge_of_adapted) | (intros; apply GlobalTheory.HodgeAt.hodge_of_adapted  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeCrystallineSequences
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

noncomputable section

namespace GlobalTheory.HodgeCrysSeq

theorem hodgeExact_at (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) : Formalism.MainNotions.WachCoordinates.HodgeExact (P.PD K) ↥LL.1 ↥(OL LL) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T₁ T₂ F h1 _ hF τ a hj
    have hs : Function.Surjective F.f := by
      have hr : LinearMap.range F.f = ⊤ := by
        rw [eq_top_iff, ← T₂.L.span, Submodule.span_le]
        intro y hy
        obtain ⟨x, -, rfl⟩ := hF y hy
        exact ⟨x, rfl⟩
      exact LinearMap.range_eq_top.1 hr
    have hst : ∀ g, LinearMap.ker F.f ≤ (LinearMap.ker F.f).comap (T₁.ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, F.equiv, LinearMap.mem_ker.1 hv, map_zero]
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1
    have := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL (LinearMap.ker F.f)
      (T₁.ρ.subrepresentation (LinearMap.ker F.f) hst) T₁.V T₁.ρ T₂.V T₂.ρ
      (LinearMap.ker F.f).subtype F.f (fun _ _ => rfl) F.equiv (LinearMap.ker F.f).injective_subtype hs
      (Submodule.range_subtype _) hdr
    exact (this.2.2 τ a).2.2.2 (Or.inr hj)
  · intro T₀ T₁ T₂ ι π hS h1
    obtain ⟨hi, hs, -, hk, -⟩ := hS
    have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi
      h1.2.2.2
    have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs
      h1.2.2.2).1
    have hr : LinearMap.range ι.f = LinearMap.ker π.f := by
      ext x
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      exact (hk x).symm
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1
    have := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f
      ι.equiv π.equiv hi hs hr hdr
    exact ⟨⟨inferInstance, inferInstance, T₀.cont, c0⟩, ⟨inferInstance, inferInstance, T₂.cont, c2⟩,
      fun τ a => (this.2.2 τ a).2.2⟩
  · intro T hT' τ a hj
    exact (GlobalTheory.TrivCrys.triv_crys_jump_zero l P AI hT K LL T.V T.ρ hT').2 τ a hj

theorem hodge_crystalline_sequences : ∀ D : D7, Formalism.MainNotions.WachCoordinates.adm14 D := by
  intro D l _ K LL
  exact hodgeExact_at l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory.HodgeCrysSeq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem htOp_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  intro l _ K C ξ a d ρ r b e hR σ z H U u hU hu
  have hσz : ∀ c : ℤ_[l], σ (zOm l c) = zOm l c := fun c => by simp [zOm]
  have hθo : ∀ w : Om l, Per.θD l (C.o w) = algebraMap (Om l) ℂ_[l] w := fun w => C.o_sec.th w

  let S : Set (Om l) := Set.range fun t : Fin d × Fin a × Fin a => σ (b t.1 t.2.1 t.2.2)
  haveI : Finite S := (Set.finite_range _).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S, hfd⟩
  have hfix : ∀ g : GQ l, g ∈ GK K' → ∀ i m k, g (σ (b i m k)) = σ (b i m k) := by
    intro g hg i m k
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg _
      (IntermediateField.subset_adjoin _ _ ⟨(i, m, k), rfl⟩)
  let B : Fin a → Matrix (Fin a) (Fin d) ℂ_[l] := fun k m i => algebraMap (Om l) ℂ_[l] (σ (b i m k))
  have hVu : IsUnit (H.V.map (Per.θD l)) := H.unit.map (Per.θD l).mapMatrix
  have col : ∀ k, u * B k * H.V.map (Per.θD l) = B k * U * H.V.map (Per.θD l) := by

    intro k
    ext m j
    let y : Fin a → Per.BdRp l := fun m => ∑ i, C.o (σ (b i m k)) * H.V i j
    let x : Fin a → Per.BdR l := fun m => ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j
    have hy : ∀ m, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * x m = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * y m) := by
      intro m
      simp only [x, y, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hq := H.Q_eq i j
      calc algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j)
          = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * H.Q i j) := by ring
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * H.V i j) := by rw [hq]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * (C.o (σ (b i m k)) * H.V i j)) := by simp only [map_mul, map_pow]; ring
    have hx : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
        ((r g).val.map σ).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x := by
      intro g hg
      funext m'
      have hσD : ∀ m, Per.σD (g : GQ l) (x m) = ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j) := by
        intro m
        simp only [x, map_sum, map_mul, PrimeEx.sigD_o, hfix _ hg]
      have e1 : ∀ i, ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) =
          ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) := by
        intro i
        have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (M m' k)))) (hR.equi g i)
        simpa [Matrix.mul_apply, Matrix.sum_apply, map_sum, map_mul, hσz] using h1
      have e2 : ∀ s, ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) = H.Q s j := by
        intro s
        have h1 := congrFun (congrFun (H.inv g g.2) s) j
        simpa [Matrix.mul_apply] using h1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply, hσD]
      calc ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j)
          = ∑ i, (∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
        _ = ∑ i, (∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [e1]
        _ = ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x m' := by simp only [e2, x]
    have h := hu K' (H.p j) H.q x y hx hy
    have hθy : (fun m => Per.θD l (y m)) = fun m => (B k * H.V.map (Per.θD l)) m j := by
      funext m'
      simp only [y, Matrix.mul_apply, Matrix.map_apply]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hθo]
    rw [hθy] at h
    have h2 := congrFun h m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_assoc u, Matrix.mul_assoc (B k), hU, ← Matrix.mul_assoc (B k), Matrix.mul_diagonal, Matrix.mul_apply, h2, mul_comm]
  have comm : ∀ k, u * B k = B k * U := by
    intro k
    have hd : IsUnit (H.V.map (Per.θD l)).det := (Matrix.isUnit_iff_isUnit_det _).1 hVu
    calc u * B k = u * B k * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by
          rw [Matrix.mul_assoc (u * B k), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = B k * U * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by rw [col k]
      _ = B k * U := by rw [Matrix.mul_assoc (B k * U), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have key : ∀ x : Fin d → ℂ_[l], u * (∑ i, x i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w)) =
      ∑ i, (U *ᵥ x) i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w) := by
    intro x
    ext m k
    have h := congrFun (congrArg (· *ᵥ x) (comm k)) m
    simp only [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, B] at h
    refine (Finset.sum_congr rfl fun x1 _ => ?_).trans (h.trans (Finset.sum_congr rfl fun c _ => ?_))
    · congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact mul_comm _ _
  have one : ∑ i, (fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map (fun w => algebraMap (Om l) ℂ_[l] (σ w)) = 1 := by
    ext m k
    have h := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Om l) ℂ_[l] (σ (M m k))) hR.one
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσz] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [h]
    by_cases hmk : m = k <;> simp [Matrix.one_apply, hmk]
  intro n
  induction n with
  | zero => simpa using one.symm
  | succ n ih => rw [pow_succ', ih, key, Matrix.mulVec_mulVec, ← pow_succ']

end GlobalTheory.BKLim
end
end

