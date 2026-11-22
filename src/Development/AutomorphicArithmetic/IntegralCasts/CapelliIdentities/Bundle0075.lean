import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0056

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEigvec
section
open Matrix IsLocalRing Polynomial

private theorem UpperTheory.Reformulated.B.Qf19.exists_eigvec {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R)
    (hu : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b))
    (hm : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R) (a : Fin 3) :
    ∃ (l : R) (v : Fin 3 → R), v a = 1 ∧ (∀ b, b ≠ a → v b ∈ maximalIdeal R) ∧ X *ᵥ v = l • v := by
  have hd : X.map (residue R) = diagonal fun b => residue R (X b b) := by
    ext b c
    by_cases h : b = c
    · subst h; simp
    · rw [diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]; exact hm b c h
  have hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0 := fun b hb => by
    rw [← map_sub]; exact ((hu a b hb.symm).map (residue R)).ne_zero
  have hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)
  have hc : X.charpoly.map (residue R) =
      (Polynomial.X - C (residue R (X a a))) *
        ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b))) := by
    rw [← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal,
      Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]
  obtain ⟨l, hl, hla⟩ := HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a)
    (by
      rw [← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]
      simp)
    (by
      change IsUnit (residue R _)
      rw [← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]
      simpa [eval_prod] using hP)
  have hla' : residue R l = residue R (X a a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hla
  set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM
  have hdet : M.det = 0 := by rw [hM, ← Matrix.eval_charpoly]; exact hl
  have hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b) := by
    ext b c
    have := congrFun (congrFun hd b) c
    by_cases h : b = c
    · subst h; simp [hM, hla']
    · rw [diagonal_apply_ne _ h] at this ⊢
      simpa [hM, diagonal_apply_ne _ h] using this
  have hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i,
      (residue R (X a a) - residue R (X j j))) b a := fun b => by
    have := (residue R).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal] at this
    exact congrFun (congrFun this b) a
  have hun : IsUnit (M.adjugate a a) := by
    rw [← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]; exact hP
  obtain ⟨u, hu'⟩ := hun
  have hker : M *ᵥ (fun b => M.adjugate b a) = 0 := by
    ext b
    have := congrFun (congrFun (mul_adjugate M) b) a
    rw [hdet, zero_smul] at this
    exact this
  refine ⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩
  · simp [← hu']
  · refine Ideal.mul_mem_left _ _ ?_
    rw [← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]
  · rw [hM, sub_mulVec, sub_eq_zero] at hker
    rw [mulVec_smul, ← hker, smul_comm l]
    congr 1
    ext b
    simp [mulVec_diagonal, hM]

theorem UpperTheory.Reformulated.B.Qf19.exists_canon :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (X : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
      (∀ (a b : Fin (3 : ℕ)), a ≠ b → IsUnit (X a a - X b b)) →
        (∀ (a b : Fin (3 : ℕ)), a ≠ b → X a b ∈ IsLocalRing.maximalIdeal R) →
          ∃ (h : GL (Fin (3 : ℕ)) R), UpperTheory.V.UnitaryThreeInertia.Canon X h := by
  intro R _ _ _ X hu hm
  choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm
  set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH
  have hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R := fun a b => by
    by_cases h : a = b
    · subst h; simp [hH, h1]
    · simpa [hH, one_apply_ne h] using h2 b a h
  have hmap : (residue R).mapMatrix H = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hhat a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, map_apply, this]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]
  have hdet : IsUnit H.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]; simp
  obtain ⟨h, hh⟩ := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hXH : X * H = H * diagonal l := by
    ext b a
    have := congrFun (h3 a) b
    rw [mul_diagonal, mul_comm]
    exact this
  refine ⟨h, ?_, fun a => ?_, ?_⟩
  · intro a b; rw [hh]; exact hhat a b
  · rw [hh]; exact h1 a
  · have : ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l := by
      rw [Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]
      simp
    rw [this]; exact isDiag_diagonal l
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInfiniteAdelicCharNeOne
section
theorem UpperTheory.Reformulated.B.Rd3.exists_infiniteAdelicChar_ne_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (w : NumberField.InfinitePlace F),
    ∃ (z : w.Completion),
      (GroundTheory.Global.infiniteAdelicChar F w : w.Completion → Circle) z ≠
        (1 : Circle) := by
  intro F _ _ w
  refine ⟨((2 * w.mult : ℕ) : w.Completion)⁻¹, fun h => ?_⟩
  have hm : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr NumberField.InfinitePlace.mult_pos.ne'
  have hx : 2 * Real.pi * -((w.mult : ℝ) * (((2 * w.mult : ℕ) : ℝ))⁻¹) = -Real.pi := by
    push_cast
    field_simp
  rw [GroundTheory.Global.infiniteAdelicChar_apply, map_inv₀, map_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.ofReal_re] at h
  have h2 := congrArg (fun c : Circle => (c : ℂ)) h
  simp only [Real.fourierChar_apply, hx, Circle.coe_one] at h2
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
  norm_num at h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemBis
section
private lemma exists_ne_zero_smul_mem_of_span_eq_top_alt {O LL V : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (h : Submodule.span LL (T : Set V) = ⊤) (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem _ hax
    · rw [mul_smul]; exact T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hd : (d : O) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : O) * a, mul_ne_zero hd ha, ?_⟩
    have key : ((d : O) * a) • c • x = n • a • x := by
      have e : ∀ (r : O) (y : V), r • y = (algebraMap O LL r) • y :=
        fun r y => (algebraMap_smul LL r y).symm
      have hnd' : c * algebraMap O LL (d : O) = algebraMap O LL n := hnd
      rw [e ((d : O) * a), e n, e a, smul_smul, smul_smul, map_mul, ← hnd']
      congr 1
      ring
    rw [key]
    exact T.smul_mem _ hax

theorem UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem :
    ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] {Qp LL O : Type} [inst_2 : Field.{0} Qp]
      [inst_3 : Field.{0} LL]
      [inst_4 :
        @Algebra.{0, 0} Qp LL (@Semifield.toCommSemiring.{0} Qp (@Field.toSemifield.{0} Qp inst_2))
          (@DivisionSemiring.toSemiring.{0} LL (@Semifield.toDivisionSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)))]
      [inst_5 : CommRing.{0} O]
      [inst_6 :
        @Algebra.{0, 0} O LL (@CommRing.toCommSemiring.{0} O inst_5)
          (@DivisionSemiring.toSemiring.{0} LL (@Semifield.toDivisionSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)))]
      [inst_7 : TopologicalSpace.{0} LL]
      (A : @Formalism.MainNotions.N.GRep G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7)
      (LA :
        @Formalism.WeaklyAdmissibleFiltrations.Lattice G inst LL inst_3 O inst_5
          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.modLL G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.ρ G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
      [@IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))]
      [@IsFractionRing.{0, 0} O (@CommRing.toCommSemiring.{0} O inst_5) LL
          (@Semifield.toCommSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)) inst_6]
      (v : @Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A),
      ∃ (a : O),
        And
          (@Ne.{1} O a
            (@OfNat.ofNat.{0} O (nat_lit 0)
              (@Zero.toOfNat0.{0} O
                (@MulZeroClass.toZero.{0} O
                  (@instMulZeroClassOfSemiring.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5)))))))
          (@Membership.mem.{0, 0} (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
            (@Submodule.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
              (@AddCommGroup.toAddCommMonoid.{0}
                (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
              (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                (@AddCommGroup.toAddCommMonoid.{0}
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Submodule.setLike.{0, 0} O
                (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                (@AddCommGroup.toAddCommMonoid.{0}
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))
            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_3 O inst_5
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.modLL G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.ρ G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A) LA)
            (@HSMul.hSMul.{0, 0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@instHSMul.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@SMulZeroClass.toSMul.{0, 0} O
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@AddZero.toZero.{0} (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                    (@AddZeroClass.toAddZero.{0}
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@AddMonoid.toAddZeroClass.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@SubNegMonoid.toAddMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddGroup.toSubNegMonoid.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@AddCommGroup.toAddGroup.{0}
                              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                              (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} O
                    (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                    (@AddMonoid.toAddZeroClass.{0}
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@SubNegMonoid.toAddMonoid.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@AddGroup.toSubNegMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddCommGroup.toAddGroup.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))))
                    (@DistribMulAction.toDistribSMul.{0, 0} O
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5)))
                      (@SubNegMonoid.toAddMonoid.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@AddGroup.toSubNegMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddCommGroup.toAddGroup.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))))
                      (@Module.toDistribMulAction.{0, 0} O
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                        (@AddCommGroup.toAddCommMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                        (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))))))
              a v)) := by
  intro G _ _ Qp LL O _ _ _ _ _ _ A LA _ _ v
  letI := A.acg
  letI := A.modLL
  letI := A.modO
  haveI := A.towO
  obtain ⟨T, _, _, _, hs⟩ := LA
  exact exists_ne_zero_smul_mem_of_span_eq_top_alt T hs v
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HaarConstOfHaarExists
section
theorem UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists :
    UpperTheory.ConvolutionTheory.T4.HaarEx → UpperTheory.ConvolutionTheory.T4.HaarConst := by
  intro H V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  have hm1 := fun v => (hm v).1
  choose a ha0 ha using H V G Gi Gv q p K hRP μ μi m hμ hμi hm1
  obtain ⟨hq, hp, hK, -⟩ := hRP
  obtain ⟨A⟩ : Nonempty (TopologicalSpace.PositiveCompacts Gi) := inferInstance
  refine ⟨a ∅, ha0 ∅, fun S => ?_⟩
  have h : a ∅ = a S :=
    UpperTheory.restricted_product_measure V G Gi Gv q (fun v => p v) (fun v => K v) μ μi m hq.measurable
      (fun v => (hp v).measurable) (fun v => (hK v).measurableSet) (fun v => (hm v).2)
      ⟨A, A.isCompact.measurableSet,
        (MeasureTheory.Measure.measure_pos_of_nonempty_interior μi A.interior_nonempty).ne',
        A.isCompact.measure_lt_top.ne⟩ ∅ S (a ∅) (a S) (ha ∅) (ha S)
  exact h ▸ ha S
end

