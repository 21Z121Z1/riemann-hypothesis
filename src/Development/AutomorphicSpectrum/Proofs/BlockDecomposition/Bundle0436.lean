import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0058
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0056
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.UnrCM

theorem algebraMap_int_ringOfIntegers_surjective (F : Type) [Field F] [NumberField F]
    (h : Module.finrank ℚ F = 1) : Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  obtain ⟨q, hq⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 (x : F)
  have hint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (algebraMap ℚ F).injective).1 (hq ▸ x.isIntegral_coe)
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  simpa using hq

theorem finrank_maximalRealSubfield_of_subsingleton (E : Type) [Field E] [NumberField E] [IsCMField E]
    [Subsingleton (InfinitePlace E)] : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have h1 : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h4 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have h5 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h5
  omega

theorem nontrivial_infinitePlace_of_forall_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hn
  haveI : Subsingleton (InfinitePlace E) := not_nontrivial_iff_subsingleton.1 hn
  have hF := finrank_maximalRealSubfield_of_subsingleton E
  have hE : Module.finrank ℚ E ≠ 1 := by
    have h5 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hF] at h5
    omega
  obtain ⟨P, hP, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := E) (𝒪 := 𝓞 E) hE
  have hbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hw := hU ⟨P, hP.isPrime, hbot⟩
  apply hram
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P) := hw
  haveI : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ _)
      (algebraMap_int_ringOfIntegers_surjective _ hF)
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P)

theorem nontrivial_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) :=
  fun E _ _ _ hU => nontrivial_infinitePlace_of_forall_isUnramifiedAt E hU

end GlobalTheory.CompanionTheory.UnrCM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
section
open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open CompanionTheory.D.LK (Pos)

namespace GlobalTheory.CompanionTheory.PairMult.TopCycQ

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem mem_omQ (lev : Fin n → ℕ) (l : Lt n) :
    l ∈ omQ lev ↔ l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omQ]

theorem insert_ne_omQ (lev : Fin n → ℕ) (s t : Bool) (i j k : Pos n)
    (ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2) (C : Finset (Lt n)) :
    insert (s, i) (insert (t, j) (C.erase ((s == t), k))) ≠ omQ lev := by
  intro e
  have hi := (mem_omQ lev _).1 (e ▸ mem_insert_self _ _)
  have hj := (mem_omQ lev _).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
  obtain ⟨t1, t2, t3⟩ := ht
  have hs : s = true := hi.1
  have htt : t = true := hj.1
  subst hs htt
  have ck : ((true == true), k) ∈ omQ lev := (mem_omQ lev _).2
    ⟨rfl, by rw [t2, t3]; exact (hi.2.trans_eq (congrArg lev t1)).trans hj.2⟩
  rw [← e] at ck
  rcases mem_insert.1 ck with h | h
  · have hk : k = i := congrArg Prod.snd h
    subst hk
    have pj := j.2
    rw [← t1, t3] at pj
    exact lt_irrefl _ pj
  · rcases mem_insert.1 h with h | h
    · have hk : k = j := congrArg Prod.snd h
      subst hk
      have pi := i.2
      rw [← t2, t1] at pi
      exact lt_irrefl _ pi
    · exact notMem_erase _ _ h

theorem topCyc : TopCyc := by
  intro n lev V _ _ E1 E2 _ v hv
  funext A
  simp only [bdq, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro s _
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    split_ifs with ht
    · rw [Module.End.mul_apply, Module.End.mul_apply, creq_app]
      split_ifs with hk
      · rw [annq_app]
        split_ifs with h1
        · exact smul_zero _
        · rw [annq_app]
          split_ifs with h2
          · simp
          · rw [topq, Pi.single_eq_of_ne (insert_ne_omQ lev s t i j k ht A), smul_zero, smul_zero, smul_zero]
      · rfl
    · rfl
  · intro l _
    show Tl E1 E2 l (annq l (topq lev v) A) = 0
    rw [annq_app]
    split_ifs with hl
    · exact map_zero _
    · by_cases e : insert l A = omQ lev
      · have hlK := (mem_omQ lev l).1 (e ▸ mem_insert_self l A)
        rw [topq, e, Pi.single_eq_same, map_smul, hv l hlK, smul_zero]
      · rw [topq, Pi.single_eq_of_ne e, smul_zero, map_zero]

end GlobalTheory.CompanionTheory.PairMult.TopCycQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSp
section
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.PairSpProof

theorem pairSp : PositivityTheory.Rg.BcB.E.E3.PairSp := by
  intro E _ _ _ a b F U₁ U₂ h₁ h₂ hfd
  classical
  set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA
  have : FiniteDimensional ℂ A := hfd
  obtain ⟨S, c, hc⟩ := PositivityTheory.Rg.Rs.SliceTensor.interp A

  let V : Submodule ℂ (GA E a → ℂ) := (U₁.map (Submodule.subtype _))
  have hAV : A ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ, e⟩ := h₁ y
    exact ⟨φ, hφ, e⟩
  have hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2) := by
    funext ⟨x, y⟩
    have hy : (fun x => F (x, y)) ∈ A := Submodule.subset_span ⟨y, rfl⟩
    have := congrFun (hc _ hy) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [hF]
  refine Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_
  obtain ⟨φ, hφ, e⟩ := hAV (c κ).2
  obtain ⟨ψ, hψ, e'⟩ := h₂ κ.1
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  funext x
  have e1 : φ.1 = (c κ : GA E a → ℂ) := e
  rw [e1, e']

end GlobalTheory.CompanionTheory.PairSpProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicElementBlockForm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ParabBlock

theorem parab_eq_blk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (p : parab (w.adicCompletion E) (two (stdSum h))), ∃ X, (p : GLw n w) = GlobalTheory.BCT.blk h w ((leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm (leviProj (w.adicCompletion E) (two (stdSum h)) p)) X := by
  intro E _ _ _ n a b h w p
  obtain ⟨m, hm⟩ : ∃ m, m = (leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (leviProj (w.adicCompletion E) (two (stdSum h)) p) := ⟨_, rfl⟩
  have h1 : ∀ i j, (m.1 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) := by
    intro i j; rw [hm]; rfl
  have h2 : ∀ i j, (m.2 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) := by
    intro i j; rw [hm]; rfl
  have h0 : ∀ (i : Fin b) (j : Fin a),
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
    intro i j
    exact mem_parab_iff.1 p.2 true false i j (by decide)
  rw [← hm]
  let B : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun i j =>
    ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j))
  refine ⟨(m.1⁻¹).val * B, ?_⟩
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val) =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) := by
    have hc : m.1.val * ((m.1⁻¹).val * B) = B := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [hc]
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (stdSum h).surjective i
    obtain ⟨j, rfl⟩ := (stdSum h).surjective j
    have hs : finSumFinEquiv.trans (finCongr h) = stdSum h := rfl
    rw [hs]
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · exact h1 i j
    · rfl
    · exact (h0 i j).symm
    · exact h2 i j
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val)) := by
    rw [hM]; exact (p : GLw n w).isUnit
  unfold GlobalTheory.BCT.blk
  simp only
  rw [dif_pos hU]
  exact Units.ext (by rw [IsUnit.unit_spec, hM])

end GlobalTheory.CompanionTheory.ParabBlock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifferenceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_twist_iso_difference : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw | exact GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationInequalityAbelianStatement
section
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relation_inequality_abelian : RelIneAb := by
  first | exact @GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb | exact GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb | (intros; apply GlobalTheory.CompanionTheory.RelIneAbProof.relIneAb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmpleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_consecutive_very_ample : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))), VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  first | exact @GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple | exact GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple | (intros; apply GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarOnWeightSpace
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.Asm

open Formalism.REAL (GlRel qdet)
open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RgCOBlock (sz shift fb)
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

theorem mem_down {S : Finset (Fin n)} (hS : ∀ a b, b ≤ a → a ∈ S → b ∈ S) (a : Fin n) :
    a ∈ S ↔ (a : ℕ) < S.card :=
  _root_.UpperTheory.Reformulated.B.DYlb8.main hS a

theorem twice_sum_Ico (m d : ℕ) :
    2 * ∑ k ∈ Finset.Ico m (m + d), (k : ℝ) = 2 * (d : ℝ) * m + d * ((d : ℝ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem level_sum (lev : Fin n → ℕ) (hm : Monotone lev) (c : ℕ) :
    2 * ∑ a ∈ univ.filter (fun a => lev a = c), ((a : ℕ) : ℝ) =
      2 * ((univ.filter fun a => lev a = c).card : ℝ) * ((univ.filter fun a => lev a < c).card : ℝ) +
        ((univ.filter fun a => lev a = c).card : ℝ) * (((univ.filter fun a => lev a = c).card : ℝ) - 1) := by
  set d := (univ.filter fun a => lev a = c).card with hd
  set m := (univ.filter fun a => lev a < c).card with hmm
  have hlow : ∀ a, lev a < c ↔ (a : ℕ) < m := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    simpa using this
  have hcard : (univ.filter fun a => lev a < c + 1).card = m + d := by
    rw [hmm, hd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro a h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
  have hup : ∀ a, lev a < c + 1 ↔ (a : ℕ) < m + d := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c + 1) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    rw [hcard] at this
    simpa using this
  have hle : m + d ≤ n := by
    rw [← hcard]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have hmap : (univ.filter fun a => lev a = c).map Fin.valEmbedding = Finset.Ico m (m + d) := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hlow a
      have h2 := hup a
      omega
    · rintro ⟨k1, k2⟩
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      have h1 := hlow ⟨k, by omega⟩
      have h2 := hup ⟨k, by omega⟩
      simp only at h1 h2
      omega
  rw [← twice_sum_Ico, ← hmap, Finset.sum_map]
  rfl

section Alg

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end Alg

section Spaces

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def cycQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppQ (inUL lev) x ∧ DegQ j x ∧ bdq E1 E2 x = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun A hA i hi => ?_, fun A hA => ?_, by rw [map_add, h3, g3, add_zero]⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), by rw [map_smul, h3, smul_zero]⟩

def bdyQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {x | ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧ bdq E1 E2 w = x}
  add_mem' := by
    rintro _ _ ⟨x, h1, h2, rfl⟩ ⟨y, g1, g2, rfl⟩
    refine ⟨x + y, fun A hA i hi => ?_, fun A hA => ?_, map_add _ _ _⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨0, fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, h1, h2, rfl⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨c • x, fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), map_smul _ _ _⟩

abbrev HQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Type :=
  cycQ lev E1 E2 j ⧸ (bdyQ lev E1 E2 j).comap (cycQ lev E1 E2 j).subtype

abbrev levL (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Bool × Fin n × Fin n) :
    Module.End ℂ (Cq n V) :=
  if lev x.2.1 = lev x.2.2 then (if x.1 then c1 E1 E2 x.2.1 x.2.2 else c2 E1 E2 x.2.1 x.2.2) else 0

abbrev fam {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W) (s : Bool) (p q : Fin n) : Module.End ℂ W :=
  ρ (FreeAlgebra.ι ℂ (s, p, q))

end Spaces

end GlobalTheory.CompanionTheory.PairMult.Asm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sl2SquareKillsVectorStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sl2_square_kills_vector : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.sl2_square_kills | exact GlobalTheory.CompanionTheory.RealCount.sl2_square_kills | (intros; apply GlobalTheory.CompanionTheory.RealCount.sl2_square_kills <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMirabolicKernelEqZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

theorem eq_zero_of_forall_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 m V _ _ τ hτ v h0 hg
  have hρ : IsSmooth (τ.comp (unipMir k (m + 1))) := GlobalTheory.T.mirabolic_restriction_unipotent_smooth k (m + 1) V τ hτ
  have hall : ∀ a : Fin (m + 1) → k,
      v ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ a ⊤) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      exact mem_chi_zero ψ τ h0
    · obtain ⟨g, hgr⟩ := GlobalTheory.T.exists_invertible_matrix_last_line_given k m a ha
      have e : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) = a := funext hgr
      have := mem_chi_row ψ τ g (hg g)
      rw [e, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at this
      exact this
  obtain ⟨N, hN⟩ := GlobalTheory.T.smooth_vector_fixed_by_small_box k (m + 1) V _ hρ v
  obtain ⟨J, hJ⟩ := GlobalTheory.T.uniform_twisted_invariance_on_ball k ψ hψ (m + 1) V _ v (addCharConductor ψ - N)
    (fun a => GlobalTheory.T.twisted_invariant_small_boxes k (m + 1) V _ (chi k ψ a) v (hall a))
  exact GlobalTheory.T.twisted_kernel_of_small_box_character k ψ hψ hψ1 (m + 1) V _ hρ v N (min J N) (min_le_right _ _) hN
    (fun a ha => hJ (min J N) (min_le_left _ _) a ha)

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjointStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spin_gl_relations_adjoint : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | exact GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEqStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_equiv_of_sup_eq : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A → Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  first | exact @GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup | exact GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup | (intros; apply GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup <;> assumption)
end

