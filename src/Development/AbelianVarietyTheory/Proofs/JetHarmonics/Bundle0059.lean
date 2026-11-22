import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Formalism.FlagUnipotentLattices.Bundle0006
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExtensionTorsion

open KernelNoTorsion

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

noncomputable def torsionHom (q : G ⟶ B) [IsMonHom q] (N : ℕ) : torsion G N ⟶ torsion B N :=
  torsionLift (torsion.ι G N ≫ q) (by rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp])

theorem torsionHom_ι (q : G ⟶ B) [IsMonHom q] (N : ℕ) :
    torsionHom q N ≫ torsion.ι B N = torsion.ι G N ≫ q :=
  torsionLift_ι _ _

theorem exists_isPullback_mulN [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P Q : Over S} {a : P ⟶ G} {b : P ⟶ torsion B N} (hP : IsPullback a b q (torsion.ι B N))
    {s : Q ⟶ P} {r : Q ⟶ torsion G N} (hQ : IsPullback s r b (torsionHom q N)) :
    ∃ (c : P ⟶ T) (t : Q ⟶ T), IsPullback s t c (mulN T N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  have hpow : ∀ {W : Over S} (x : W ⟶ torsion G N), (x ≫ torsion.ι G N) ^ N = 1 := fun x => by
    rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]
  obtain ⟨c, hc⟩ := ex (a ^ N) (by
    rw [MonObj.pow_comp, hP.w, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one])
  have hsr : s ≫ a ≫ q = r ≫ torsion.ι G N ≫ q := by
    rw [hP.w, ← Category.assoc, hQ.w, Category.assoc, torsionHom_ι]
  obtain ⟨t, ht⟩ := ex ((s ≫ a) / (r ≫ torsion.ι G N)) (by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [comp_mulN, MonObj.pow_comp, ht, div_pow, hpow, div_one, Category.assoc, hc,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, comp_mulN]
    have hg : ((W.fst ≫ a) / (W.snd ≫ i)) ^ N = 1 := by
      rw [div_pow, ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, MonObj.comp_pow, div_self']
    have hl : W.fst ≫ b = torsionLift _ hg ≫ torsionHom q N := by
      apply torsion_hom_ext
      rw [Category.assoc, Category.assoc, torsionHom_ι, ← Category.assoc (torsionLift _ hg),
        torsionLift_ι, GrpObj.div_comp, Category.assoc, Category.assoc, hiq, MonObj.comp_one,
        div_one, hP.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, ← Category.assoc, hQ.lift_fst,
        hQ.lift_snd, torsionLift_ι, div_div_cancel]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      apply torsion_hom_ext
      rw [hQ.lift_snd, torsionLift_ι, ← h1, ← h2, Category.assoc, Category.assoc, Category.assoc,
        ht, GrpObj.comp_div, div_div_cancel]

theorem torsionHom_of_mulN (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ) (h : Pr (mulN T N).left) :
    Pr (torsionHom q N).left := by
  have hP := IsPullback.of_hasPullback q (torsion.ι B N)
  have hQ := IsPullback.of_hasPullback (pullback.snd q (torsion.ι B N)) (torsionHom q N)
  obtain ⟨c, t, H⟩ := exists_isPullback_mulN i q hk N hP hQ
  have hP' := hP.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end ExtensionTorsion

open ExtensionTorsion in

theorem isFinite_flat_torsion_of_isGt :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G], E.IsGt G → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion E.B N).hom → Flat (torsion E.B N).hom → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom := by
  rintro S E G _ _ ⟨D⟩ N hN h1 h2
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have a1 : Flat (torsionHom D.q N).left :=
    torsionHom_of_mulN @Flat D.i D.q D.isKernel N hl
  have a2 : IsAffineHom (torsionHom D.q N).left :=
    torsionHom_of_mulN @IsAffineHom D.i D.q D.isKernel N inferInstance
  have a3 : UniversallyClosed (torsionHom D.q N).left :=
    torsionHom_of_mulN @UniversallyClosed D.i D.q D.isKernel N inferInstance
  have a4 : LocallyOfFiniteType (torsionHom D.q N).left :=
    torsionHom_of_mulN @LocallyOfFiniteType D.i D.q D.isKernel N inferInstance
  have a5 : IsFinite (torsionHom D.q N).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  rw [← Over.w (torsionHom D.q N)]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LoweringBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PieriBound

theorem bound_cast (k M n : ℕ) (hn : n = k + M) (lam mu : Fin n → ℝ) (u : ℕ → ℝ) (b bv ga q0 : ℝ) (s : Fin n)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (h1 : StrictAnti lam) (h2 : ∀ a c, ∃ z : ℤ, lam a - lam c = (z : ℝ))
    (h3 : ∀ a, ∀ i ∈ Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2)
    (h4 : ∀ a : Fin n, a.val < k → lam a < u (a.val + 1))
    (h5 : ∀ a : Fin n, a.val + 1 < k → u (a.val + 2) < lam a)
    (h6 : ∀ a : Fin n, a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8)
    (h7 : ∀ a : Fin n, k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv)
    (h8 : ∀ a, |lam a| ≤ b) (h9 : ∀ i ∈ Icc 1 k, |u i| ≤ b)
    (h10 : ∀ a c : Fin n, a < c → c.val + 1 < k → ga ≤ lam a - lam c) (h11 : 4 ≤ ga)
    (h12 : ∀ a, ∃ z : ℤ, mu a - lam a = (z : ℝ)) (h13 : StrictAnti mu)
    (h14 : ∑ a, |mu a - lam a| ≤ q0) (h15 : q0 ≤ ga / 8) (h16 : q0 ≤ bv / 4) (h17 : q0 ≤ b)
    (h18 : ∀ s', s' ≠ s → mu s - 1 ≠ mu s') :
    (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2 := by
  subst hn
  have hmem : ∀ i : Fin k, (i : ℕ) + 1 ∈ Icc 1 k := fun i => by
    rw [Finset.mem_Icc]; have := i.2; omega
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.sup_l2_ratio_majorant k M lam mu (fun i => u (i.val + 1)) b bv ga q0 s hk hM
    ⟨h1, h2, fun a i => h3 a _ (hmem i), fun i => h4 (Fin.castAdd M i) i.2,
      fun i j hij => by
        have := h5 (Fin.castAdd M i) (by have := j.2; simp only [Fin.val_castAdd]; omega)
        simp only [Fin.val_castAdd] at this
        show u (j.val + 1) < _
        rw [← hij]; exact this,
      h6, h7, h8, fun i => h9 _ (hmem i), h10, h11, h12, h13, h14, h15, h16, h17⟩ h18
  have e : (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) = ∏ i : Fin k, |mu s - 1 / 2 - u (i.val + 1)| := by
    rw [Fin.prod_univ_eq_prod_range (fun i => |mu s - 1 / 2 - u (i + 1)|) k, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun i => |mu s - 1 / 2 - u i|) 0 k 1]
    rfl
  rw [e]; exact key

theorem lowering_bound : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → ∀ s, (∏ i ∈ Icc 1 k, |lam s + (ν s : ℝ) - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| ≤ b ^ 4 := by
  intro k r lam u b bv ga h q0 hN ν hν s
  obtain ⟨⟨hb, hbv, -, hq, -⟩, hf⟩ := GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN
  obtain ⟨-, -, -, hgap⟩ := hf ν hν
  obtain ⟨hk, hHC, h3, h4, h5, h6, h7, h8, h9, h10, -, -, hga, -, hbig⟩ := hN
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have key := bound_cast k (2 * r + 1) (2 * r + k + 1) (by omega) lam (fun a => lam a + (ν a : ℝ)) u b bv ga q0 s hk
    (by omega) hHC.1
    (fun a c => by
      obtain ⟨m, hm⟩ := hHC.2 a
      obtain ⟨m', hm'⟩ := hHC.2 c
      exact ⟨m - m', by push_cast at hm hm' ⊢; linarith⟩) h3 h4 h5 h6 h7 h8 h9 h10 (by linarith)
    (fun a => ⟨ν a, by ring⟩) (fun a c hac => by have := hgap a c hac; show _ < _; linarith)
    (by
      have : ((n1 ν : ℕ) : ℝ) ≤ q0 := by exact_mod_cast hν
      refine le_trans (le_of_eq ?_) this
      unfold n1
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      simp)
    (by linarith) (by linarith) (by linarith)
    (fun t ht => by
      rcases lt_or_gt_of_ne ht with hlt | hlt
      · have := hgap t s hlt
        intro e; linarith
      · have := hgap s t hlt
        intro e; linarith)
  refine key.trans ?_
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hb0 : (0 : ℝ) ≤ b := by linarith
  split_ifs
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hkn : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hp : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 :=
      le_self_pow₀ (by linarith) (by norm_num)
    have h64 : 64 * Real.exp 1 * Real.sqrt k ≤ b := by
      have : Real.exp 1 * Real.sqrt k ≤ 3 * k := mul_le_mul he hs (Real.sqrt_nonneg _) (by norm_num)
      norm_num at hbig hp hkn ⊢
      nlinarith
    calc _ ≤ b * b ^ 3 := mul_le_mul_of_nonneg_right h64 (by positivity)
      _ = b ^ 4 := by ring
  · have h16 : 16 * Real.exp 1 ≤ b ^ 2 := by nlinarith
    calc _ ≤ b ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = b ^ 4 := by ring

end GlobalTheory.PieriBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorRowExpansionEigenFunctional
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem qminor_row_step_under_functional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hab hl
  have hA : Function.Injective (Fin.cons a0 a' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨ha0, ha'⟩
  have hB : Function.Injective (Fin.cons b0 b' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨hb0, hb'⟩
  have hrB : Set.range b = Set.range (Fin.cons b0 b' : Fin (t + 1) → Fin n) := by
    rw [Fin.range_cons]; exact hrb
  obtain ⟨e, he, hq⟩ := GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq (Module.End ℂ M) n (t + 1) E a (Fin.cons a0 a') b (Fin.cons b0 b') hE
    ha hA hb hB (by rw [Fin.range_cons]; exact hra) hrB
  refine ⟨e, he, fun u v => ?_⟩
  have key : ∀ (j : Fin (t + 1)) (w : ℂ) (x : M),
      l (Formalism.REAL.Tm E w a0 ((Fin.cons b0 b' : Fin (t + 1) → Fin n) j) x) = (if j = 0 then p else 0) • l x := by
    intro j w x
    have hmem : (Fin.cons b0 b' : Fin (t + 1) → Fin n) j ∈ Set.range b := by
      rw [hrB]; exact ⟨j, rfl⟩
    have hne : a0 ≠ (Fin.cons b0 b' : Fin (t + 1) → Fin n) j := fun h => hab (h ▸ hmem)
    obtain ⟨k, hk⟩ := hmem
    have hiff : b k = b0 ↔ j = 0 := by
      rw [hk]
      exact ⟨fun h => hB (by simpa using h), fun h => by subst h; rfl⟩
    unfold Formalism.REAL.Tm
    rw [if_neg hne, zero_add, ← hk, hl k x]
    simp only [hiff]
  rw [hq u, quantum_minor_row_expansion.1 (Module.End ℂ M) n t E hE, LinearMap.smul_apply, map_smul, LinearMap.sum_apply,
    map_sum, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero, mul_smul]
  · congr 1
    have h0 := key 0
    simp only [Fin.cons_zero, if_true] at h0
    simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply, Fin.cons_zero, h0,
      Fin.succAbove_zero]
    rfl
  · intro j _
    rw [← zsmul_eq_mul, LinearMap.smul_apply, map_zsmul, Module.End.mul_apply, Fin.cons_zero, key,
      if_neg (Fin.succ_ne_zero j), zero_smul, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg _

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) := by
  obtain ⟨C, Ws, h1, h2⟩ := h
  exact ⟨max C 0, Ws, le_max_right _ _, h1, fun v hv => (h2 v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_norm_nonneg R Ws v))⟩

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B := by
  obtain ⟨C, Ws, _, h1, h2⟩ := h
  exact ⟨C, Ws, h1, fun v hv => (hle v hv).trans (h2 v hv)⟩

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  obtain ⟨C', Ws', h0', h1', h2'⟩ := hg
  refine ⟨C + C', Ws ++ Ws', add_nonneg h0 h0', ?_, fun v hv => ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact h1 w h
    · exact h1' w h
  · have a := h2 v hv
    have b := h2' v hv
    have c := sum_norm_nonneg R Ws v
    have d := sum_norm_nonneg R Ws' v
    rw [List.map_append, List.sum_append]
    nlinarith [mul_nonneg h0 d, mul_nonneg h0' c]

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  refine ⟨a * C, Ws, mul_nonneg ha h0, h1, fun v hv => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 v hv) ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) := by
  induction Ws with
  | nil => exact ⟨0, [], le_rfl, by simp, fun v _ => by simp⟩
  | cons w Ws ih =>
    have h1 := semiBd_of_cw R (hT.cont w (hWs w List.mem_cons_self))
    have h2 := ih (fun w' hw' => hWs w' (List.mem_cons_of_mem _ hw'))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := semiBd_of_cw R' hB
  exact cw_of_semiBd R ((semiBd_sum hT Ws h1).mul h0) (fun v hv => h2 _ (hT.mem v hv))

theorem smMap_comp {R R' R'' : Rep k r} {T : R.H → R'.H} {T' : R'.H → R''.H}
    (hT : SmMap R R' T) (hT' : SmMap R' R'' T') : SmMap R R'' (fun v => T' (T v)) where
  mem v hv := hT'.mem _ (hT.mem v hv)
  add v hv w hw := by
    rw [hT.add v hv w hw, hT'.add _ (hT.mem v hv) _ (hT.mem w hw)]
  smul a v hv := by
    rw [hT.smul a v hv, hT'.smul a _ (hT.mem v hv)]
  cont W hW := cw_comp (Bm := fun v => dsigW (k := k) (r := r) R''.σ W (T' v)) hT (hT'.cont W hW)

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem dsigW_mem (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W v ∈ R.sm := by
  induction W with
  | nil => exact hv
  | cons X W ih =>
    exact ((GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X (hW X List.mem_cons_self)).1 _
      (ih (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)))).1

theorem dsig_lin (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ)
    {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (a • v + w) =
      a • dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ X w := by
  have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).1
  have h1 := ((h v hv).2.const_smul a).add (h w hw).2
  refine HasDerivAt.deriv ?_
  convert h1 using 1
  funext t
  simp

theorem dsigW_lin (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v + w) =
      a • dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show dsig R.σ X (dsigW R.σ W (a • v + w)) = _
    rw [ih hW']
    exact dsig_lin hK hR (hW X List.mem_cons_self) a (dsigW_mem hK hR W hW' hv) (dsigW_mem hK hR W hW' hw)

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) := by
  obtain ⟨hu, hi, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have e1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
      = gᴴ * Xᴴ * ((g⁻¹)ᴴ * Hpk k r) + (Hpk k r * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem norm_sigma (hR : R.IsDS ε mu) {g : Mx k r} (hg : g ∈ GG k r) (v : R.H) : ‖R.σ g v‖ = ‖v‖ := by
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hR.2
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hm := hds.2.2.1.2.1 (P₀ * g * P₀⁻¹) hx' v
  have e2 : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e2] at hm
  exact hm

theorem dsigW_sigma (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) {g : Mx k r} (hg : g ∈ GG k r) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hW'' : ∀ Y ∈ W.map (fun X => g⁻¹ * X * g), InLieHpk k r Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW' Z hZ)
    have hdet : IsUnit g.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR _ (inLie_conj hg (hW X List.mem_cons_self))).2.1 _
      (dsigW_mem hK hR _ hW'' hv) g hg
    rw [e] at h
    show dsig R.σ X (dsigW R.σ W (R.σ g v)) = R.σ g (dsig R.σ (g⁻¹ * X * g) _)
    rw [ih hW', h]

theorem smMap_sigma (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) {g : Mx k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) where
  mem v hv := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv g hg
  add v _ w _ := map_add _ _ _
  smul a v _ := map_smul _ _ _
  cont W hW := by
    refine ⟨1, [W.map fun X => g⁻¹ * X * g], ?_, fun v hv => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW Z hZ)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_sigma hK hR hg W hW hv, norm_sigma hR hg]

theorem smMap_lin (hK : PI.KFinSmooth) {R₀ : Rep k r} (hR : R.IsDS ε mu) {T T' : R₀.H → R.H} (a : ℂ)
    (hT : SmMap R₀ R T) (hT' : SmMap R₀ R T') : SmMap R₀ R (fun v => a • T v + T' v) where
  mem v hv := Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a (hT.mem v hv)) (hT'.mem v hv)
  add v hv w hw := by
    rw [hT.add v hv w hw, hT'.add v hv w hw, smul_add]
    abel
  smul b v hv := by
    rw [hT.smul b v hv, hT'.smul b v hv, smul_add, smul_comm]
  cont W hW := by
    refine cw_of_semiBd R₀ (((semiBd_of_cw R₀ (hT.cont W hW)).mul (norm_nonneg a)).add
      (semiBd_of_cw R₀ (hT'.cont W hW))) (fun v hv => ?_)
    rw [dsigW_lin hK hR W hW a (hT.mem v hv) (hT'.mem v hv)]
    exact (norm_add_le _ _).trans (by rw [norm_smul])

end DS

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → R''.IsDS ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  intro hK k r ε mu mu' mu'' R R' R'' hR hR' _
  exact ⟨fun g hg => smMap_sigma hK hR hg, fun T T' hT hT' => smMap_comp hT hT',
    fun T T' a hT hT' => smMap_lin hK hR' a hT hT', fun Wp _ T Bm hT hB => cw_comp hT hB⟩

end GlobalTheory.SmMapAct
end

