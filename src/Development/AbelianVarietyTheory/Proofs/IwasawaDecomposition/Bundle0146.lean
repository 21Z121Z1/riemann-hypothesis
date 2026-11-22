import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFinite
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory

theorem finite_latticeCurve_torsion (L : PeriodPair) {n : ℕ} (hn : n ≠ 0) :
    {P : (latticeCurve L).toAffine.Point | n • P = 0}.Finite := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hz : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine (((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image
    (fun p : ℤ × ℤ => latticePoint L ((p.1 * L.ω₁ + p.2 * L.ω₂) / n))).subset ?_
  intro P hP
  obtain ⟨z, rfl⟩ := latticePoint_surjective L P
  have h1 : latticePoint L (n • z) = 0 := by
    rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
  rw [latticePoint_eq_zero_iff] at h1
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩,
    ⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩⟩, ?_⟩
  dsimp only
  rw [latticePoint_eq_iff, PeriodPair.mem_lattice]
  refine ⟨-(a / n), -(b / n), ?_⟩
  have ea : (a : ℂ) = ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a n).symm
  have eb : (b : ℂ) = ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b n).symm
  rw [nsmul_eq_mul] at hab
  rw [Int.cast_neg, Int.cast_neg]
  generalize ((a % n : ℤ) : ℂ) = a₁, ((a / n : ℤ) : ℂ) = a₂, ((b % n : ℤ) : ℂ) = b₁,
    ((b / n : ℤ) : ℂ) = b₂ at ea eb ⊢
  rw [ea, eb] at hab
  field_simp
  linear_combination -hab

theorem finite_complex_torsion_points (W : WeierstrassCurve ℂ) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.toAffine.Point | n • P = 0}.Finite := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  refine ((finite_latticeCurve_torsion L hn).image e).subset ?_
  intro P hP
  refine ⟨e.symm P, ?_, e.apply_symm_apply P⟩
  have hP' : n • P = 0 := hP
  show n • e.symm P = 0
  rw [← map_nsmul, hP', map_zero]

theorem finite_torsionCoords :
    ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  intro W _ n hn
  have h := finite_complex_torsion_points W hn
  let fx : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some x _ _ => x
  let fy : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some _ y _ => y
  refine ((h.image fx).union (h.image fy)).subset ?_
  rintro z ⟨x, y, hxy, h0, rfl | rfl⟩
  · exact Or.inl ⟨_, h0, rfl⟩
  · exact Or.inr ⟨_, h0, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.EtaUnitArg

theorem denseRange_atInf_single {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) :
    DenseRange (atInf w : Lˣ → (w.Completion)ˣ) := by
  classical
  have hs : Function.Surjective (fun u : ∀ v : InfinitePlace L, (v.Completion)ˣ => u w) := fun z =>
    ⟨Function.update (1 : ∀ v : InfinitePlace L, (v.Completion)ˣ) w z, by simp⟩
  exact hs.denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf L) (continuous_apply w)

open Classical in
theorem locInf_eq {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) (z : (w.Completion)ˣ) :
    Units.map (Formalism.L2.NC.locInf w) z = infIdele L w z := by
  apply Units.ext
  rfl

theorem etaT_isUnitArg : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  intro R H χ hχ h hh g f hf hfE z
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hloc := (GlobalTheory.InfTypeLocal.infType_iff_local H.E (R.Psi) (embPsi H) hcm.bij χ.1 χ.2.1
    (fun _ => 1)).1 (fun k => hχ.inf k) g
  have key : (fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
      ((χ.1 (infIdele H.E _ z) : ℂˣ) : ℂ)) =
      fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
        f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) /
          ((‖f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion)‖ : ℝ) : ℂ) := by
    refine (denseRange_atInf_single _).equalizer ?_ ?_ ?_
    · exact Units.continuous_val.comp (χ.2.1.comp (GlobalTheory.InfTypeLocal.continuous_infIdele _ _))
    · have h1 := hf.comp Units.continuous_val
      have h2 : ∀ u : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ,
          f (u : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) ≠ 0 := fun u =>
        (_root_.map_ne_zero _).2 u.ne_zero
      exact h1.div (Complex.continuous_ofReal.comp h1.norm) fun u => by exact_mod_cast norm_ne_zero_iff.2 (h2 u)
    · funext k
      have e : f ((atInf _ k : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ) :
          (InfinitePlace.mk (H.emb (g : R.GG))).Completion) = H.emb (g : R.GG) k := hfE k
      simp only [Function.comp_apply]
      rw [e]
      have := hloc k
      exact this.trans (zpow_one _)
  rw [locInf_eq, hh]
  exact congrFun key z

end GlobalTheory.EtaUnitArg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldLowerBounds
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.CoeffFieldLower

theorem finiteDimensional_muK_one (l : ℕ) [Fact l.Prime] : FiniteDimensional ℚ_[l] (muK l 1) := by
  classical
  have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  have hfin : ({x : PadicAlgCl l | x ^ (l ^ 1) = 1}).Finite :=
    (nthRoots (l ^ 1) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl]; exact hx
  have := hfin.to_subtype
  show FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | x ^ (l ^ 1) = 1})
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

open Classical in

def bridgeLow (D : D7) (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E)) : Loc.FinExt l :=
  if hw : w ∈ placesOver D.host.E l then
    (Classical.choose_spec (GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w))).choose
  else ⟨⊥, inferInstance⟩

def low (D : D7) : Big D := fun l hl j =>
  haveI := hl
  ⟨IntermediateField.adjoin ℚ_[l] (Set.range j) ⊔ muK l 1 ⊔
      ⨆ w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset, (bridgeLow D l w).1, by
    have := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range j
    have := finiteDimensional_muK_one l
    have : ∀ w, FiniteDimensional ℚ_[l] (bridgeLow D l w).1 := fun w => (bridgeLow D l w).2
    infer_instance⟩

theorem exists_low : ∀ (D : D7), ∃ c0 : Big D, ∀ (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l), (∀ x, j x ∈ (c0 l j).1) ∧ muK l 1 ≤ (c0 l j).1 ∧ ∀ K0 : Loc.FinExt l, (c0 l j).1 ≤ K0.1 → ∀ w ∈ placesOver D.host.E l, ∃ Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL K0), ∀ x, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1 := by
  intro D
  refine ⟨low D, fun l _ j => ⟨fun x => ?_, ?_, fun K0 hK0 w hw => ?_⟩⟩
  · have h1 : IntermediateField.adjoin ℚ_[l] (Set.range j) ≤ (low D l j).1 := le_sup_left.trans le_sup_left
    exact h1 (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact le_sup_right.trans le_sup_left
  · have hex := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
    have hspec := (Classical.choose_spec hex).choose_spec
    have hL : (bridgeLow D l w).1 ≤ K0.1 := by
      refine le_trans ?_ hK0
      refine le_trans ?_ le_sup_right
      have hmem : w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset := by simpa using hw
      exact le_iSup₂ (f := fun w (_ : w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset) =>
        (bridgeLow D l w).1) w hmem
    have e : bridgeLow D l w = (Classical.choose_spec hex).choose := dif_pos hw
    have hL' : (Classical.choose_spec hex).choose.1 ≤ K0.1 := e ▸ hL
    obtain ⟨Bw, hBj, -⟩ := hspec.2 K0 hL'
    exact ⟨Bw, fun x => by rw [hBj]; exact hspec.1 x⟩

end GlobalTheory.CoeffFieldLower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompletionEquiv
section
open NumberField IsDedekindDomain IsLocalRing Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.GO.PlWitt
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaceOrbit

theorem exists_hom_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete J B] (f : R →+* A) (g : R →+* B) (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k → g x ∈ J ^ k) :
    ∃ h : A →+* B, ∀ (k : ℕ) a x, a - f x ∈ I ^ k → h a - g x ∈ J ^ k := by
  have hsur : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (I ^ k)).comp f) := fun k y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hs k a
    exact ⟨x, (Ideal.Quotient.eq.2 hx).symm⟩
  let u : (k : ℕ) → A ⧸ I ^ k →+* B ⧸ J ^ k := fun k =>
    RingHom.liftOfSurjective _ (hsur k) ⟨(Ideal.Quotient.mk (J ^ k)).comp g, fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hk k x (Ideal.Quotient.eq_zero_iff_mem.1 hx))⟩
  let φ : (k : ℕ) → A →+* B ⧸ J ^ k := fun k => (u k).comp (Ideal.Quotient.mk _)
  have hφ : ∀ k a x, a - f x ∈ I ^ k → φ k a = Ideal.Quotient.mk _ (g x) := fun k a x h => by
    change u k (Ideal.Quotient.mk _ a) = _
    rw [Ideal.Quotient.eq.2 h]
    exact RingHom.liftOfRightInverse_comp_apply ((Ideal.Quotient.mk (I ^ k)).comp f) _ _ _ x
  have hc : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (φ n) = φ m := by
    intro m n h
    refine RingHom.ext fun a => ?_
    obtain ⟨x, hx⟩ := hs n a
    rw [RingHom.comp_apply, hφ n a x hx, hφ m a x (Ideal.pow_le_pow_right h hx)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J φ hc, fun k a x h => ?_⟩
  rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hφ k a x h]

theorem eq_of_forall_pow {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {a b : A}
    (h : ∀ k : ℕ, a - b ∈ I ^ k) : a = b :=
  sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h k)

theorem exists_equiv_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B] (f : R →+* A) (g : R →+* B)
    (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k) (hs' : ∀ (k : ℕ) (b : B), ∃ x, b - g x ∈ J ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k ↔ g x ∈ J ^ k) : ∃ e : A ≃+* B, ∀ x, e (f x) = g x := by
  obtain ⟨h, hh⟩ := exists_hom_of_dense I J f g hs fun k x => (hk k x).1
  obtain ⟨h', hh'⟩ := exists_hom_of_dense J I g f hs' fun k x => (hk k x).2
  refine ⟨RingEquiv.ofRingHom h h' (RingHom.ext fun b => eq_of_forall_pow J fun k => ?_)
    (RingHom.ext fun a => eq_of_forall_pow I fun k => ?_), fun x => eq_of_forall_pow J fun k => ?_⟩
  · obtain ⟨x, hx⟩ := hs' k b
    simpa using sub_mem (hh k _ x (hh' k b x hx)) hx
  · obtain ⟨x, hx⟩ := hs k a
    simpa using sub_mem (hh' k _ x (hh k a x hx)) hx
  · exact hh k _ x (by simp)

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [hp : Fact p.Prime]

theorem exists_completion_equiv {v : HeightOneSpectrum (𝓞 F)} {i : F →+* Qn p n} (h : Good v i) :
    ∃ e : Qn p n ≃+* v.adicCompletion F, (∀ x : F, e (i x) = algebraMap F _ x) ∧
      ∀ y, y ∈ Set.range (algebraMap (Wn p n) (Qn p n)) ↔ e y ∈ v.adicCompletionIntegers F := by
  have hint := h.intAt
  have hd := h.dense
  obtain ⟨g, hg, -, hk⟩ := h
  have hinj := IsFractionRing.injective (Wn p n) (Qn p n)
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by rw [hk, map_natCast, cc_eq_zero]
  have hval : ∀ x : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) x : v.adicCompletionIntegers F) :
      v.adicCompletion F) = v.valuation F (x : F) := fun x => by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hpF : ∀ k : ℕ, ((p : F) ^ k) ≠ 0 := fun k => pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hvp : ∀ k : ℕ, Valued.v ((((p : v.adicCompletionIntegers F) ^ k : v.adicCompletionIntegers F)) :
      v.adicCompletion F) = v.valuation F ((p : F) ^ k) := fun k => by
    simpa using hval ((p : 𝓞 F) ^ k)
  have hvp0 : ∀ k : ℕ, v.valuation F ((p : F) ^ k) ≠ 0 := fun k => by simpa using hpF k
  haveI : IsAdicComplete (Ideal.span {(p : v.adicCompletionIntegers F)}) (v.adicCompletionIntegers F) :=
    (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ (by
      have := hval p
      rw [map_natCast] at this
      rw [this]
      exact (v.valuation_lt_one_iff_mem (K := F) _).2 hpv)
  obtain ⟨e, he⟩ := exists_equiv_of_dense (Ideal.span {(p : Wn p n)}) (Ideal.span {(p : v.adicCompletionIntegers F)})
    g (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    (fun k a => by
      obtain ⟨x, z, hx⟩ := hd a k
      rw [hg] at hx
      exact ⟨x, by rw [hinj hx, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact ⟨-z, by ring⟩⟩)
    (fun k b => by
      obtain ⟨x, hx⟩ := Idele.exists_valued_sub_le v (a := (b : v.adicCompletion F)) b.2
        (-WithZero.log (v.valuation F ((p : F) ^ k))).toNat
      refine ⟨x, ?_⟩
      rw [Ideal.span_singleton_pow, GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp]
      refine le_trans hx ?_
      conv_rhs => rw [← WithZero.exp_log (hvp0 k)]
      rw [WithZero.exp_le_exp]
      omega)
    (fun k x => by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
        GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp, hval,
        ← div_le_one₀ (zero_lt_iff.2 (hvp0 k)), ← map_div₀, ← GlobalTheory.UnramCompletion.intAt_iff, hint,
        Ideal.mem_span_singleton']
      refine exists_congr fun y => ?_
      rw [map_div₀, eq_div_iff ((_root_.map_ne_zero i).2 (hpF k)), hg, ← hinj.eq_iff]
      simp)
  refine ⟨IsFractionRing.ringEquivOfRingEquiv e, fun x => ?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · have : ((IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).toRingHom.comp i) =
        algebraMap F (v.adicCompletion F) :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun x => by
        change IsFractionRing.ringEquivOfRingEquiv e (i (x : F)) = _
        rw [hg, IsFractionRing.ringEquivOfRingEquiv_algebraMap, he]
        rfl)
    exact RingHom.congr_fun this x
  · rintro ⟨w, rfl⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact (e w).2
  · refine ⟨e.symm ⟨_, hy⟩, (IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).injective ?_⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, e.apply_symm_apply]
    rfl

theorem exists_first_frame {E : Type} [Field E] [NumberField E] [Algebra F E] {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) :
    ∃ fr : GL (Fin k) (w.adicCompletion F), ∀ t : Fin k → w.adicCompletion F,
      (∃ x ∈ Formalism.L2.Herm.locL w Λ, ∀ a, (φ (x a)).1 = t a) ↔
        ∀ a, ((fr⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  obtain ⟨B, -, -, hB, -⟩ := GlobalTheory.DualFrame.exists_dual_frames F E (AlgHom.id F E) k 1 (by simp) Λ hfin hsp w
  let π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom
  have hinv : (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      ((B⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _).map π := by
    rw [← map_inv]; rfl
  refine ⟨bc π B, fun t => ⟨?_, fun hu => ?_⟩⟩
  · rintro ⟨x, hx, hxt⟩ a
    have ht : t = π ∘ x := funext fun a => (hxt a).symm
    rw [ht, hinv, ← RingHom.map_mulVec]
    refine Formalism.MainNotions.Gaps.Loc.fst_int w φ halg _ ((hB _).1 ?_ a)
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx
  · refine ⟨_, (hB fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)).2
      fun a => Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (hu a), fun a => ?_⟩
    refine (RingHom.map_mulVec π _ _ a).trans ?_
    have : (π ∘ fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)) =
        ((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t := funext fun a => congrArg Prod.fst (halg _)
    rw [this]
    change ((bc π B).1 *ᵥ _) a = _
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

end GlobalTheory.PlaceOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordsOfMemAdjoin
section
namespace GlobalTheory.CoordsOfMemAdjoin

open IntermediateField

theorem exists_coords_of_mem_adjoin {F : Type*} [Field F] [Algebra ℚ F] {s : F} {c : ℚ}
    (hs : s ^ 2 = algebraMap ℚ F c) {x : F} (hx : x ∈ ℚ⟮s⟯) :
    ∃ a b : ℚ, x = algebraMap ℚ F a + algebraMap ℚ F b * s := by
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set F) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    refine ⟨0, 1, ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    simp
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a + a', b + b', ?_⟩
    simp only [map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add, map_mul, ← hs]
    ring

theorem exists_rat_coords {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {x : H.E} (hx : x ∈ H.K) :
    ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD := by
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hs : H.sqrtMinusD ^ 2 = algebraMap ℚ H.E (-(H.d : ℚ)) := by
    rw [map_neg, map_natCast]
    exact hb
  obtain ⟨a, b, h⟩ := exists_coords_of_mem_adjoin hs hx
  exact ⟨a, b, by simpa only [eq_ratCast] using h⟩

end GlobalTheory.CoordsOfMemAdjoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorPowPrimeOneModModulus
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem exists_unif_one_mod {R : Type} [CommRing R] [IsDedekindDomain R] (𝔮 : Ideal R) (h𝔮 : 𝔮 ≠ ⊥)
    (v : HeightOneSpectrum R) : ∃ c : R, c ∈ v.asIdeal ∧ c ∉ v.asIdeal ^ 2 ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.asIdeal ∣ 𝔮 → c - 1 ∈ w.asIdeal := by
  classical
  have hfin := Ideal.finite_factors h𝔮
  let S : Finset (HeightOneSpectrum R) := hfin.toFinset.erase v
  have hcop : IsCoprime (v.asIdeal ^ 2) (∏ w ∈ S, w.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun w hw => ?_)
    have hne : v.asIdeal ≠ w.asIdeal := fun h => (Finset.ne_of_mem_erase hw) (HeightOneSpectrum.ext h).symm
    exact Ideal.isCoprime_iff_sup_eq.2 (v.isMaximal.coprime_of_ne w.isMaximal hne)
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  rw [pow_one] at hπ1
  refine ⟨π * b + a, ?_, ?_, fun w hw hd => ?_⟩
  · exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ hπ1) (Ideal.pow_le_self two_ne_zero ha)
  · intro hc
    apply hπ2
    have : π = (π * b + a) + a * (π - 1) := by linear_combination (-π) * hab
    rw [this]
    exact Ideal.add_mem _ hc (Ideal.mul_mem_right _ _ ha)
  · have hS : w ∈ S := Finset.mem_erase.2 ⟨hw, hfin.mem_toFinset.2 hd⟩
    have hb' : b ∈ w.asIdeal := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hS) hb
    have : π * b + a - 1 = b * (π - 1) := by linear_combination hab
    rw [this]
    exact Ideal.mul_mem_right _ _ hb'

theorem exists_gen_pow_prime_one_mod (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ) (h𝔮 : 𝔮 ≠ ⊥)
    (H : ∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α})
    (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ,
      FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_unif_one_mod 𝔮 h𝔮 v
  have hc0 : c ≠ 0 := by rintro rfl; exact hc2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc1)
  have hcJ : c ∈ v.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self c
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hcJ
    exact hc0 hcJ
  have hcop : IsCoprime J 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm0 : m ≠ ⊥ := fun h0 => h𝔮 (le_bot_iff.1 (h0 ▸ le_sup_right.trans hle))
    let w : HeightOneSpectrum (𝓞 L) := ⟨m, hm.isPrime, hm0⟩
    have hJm : J ≤ m := le_sup_left.trans hle
    by_cases hw : w = v
    · apply hc2
      have : v.asIdeal = m := hw ▸ rfl
      rw [sq]
      exact Ideal.mul_mono_right (this ▸ hJm) hcJ
    · have h1 : c - 1 ∈ m := hc3 w hw (Ideal.dvd_iff_le.2 (le_sup_right.trans hle))
      have h2 : c ∈ m := hJm (Ideal.le_of_dvd (dvd_mul_left J v.asIdeal) hcJ)
      exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h2 h1))
  obtain ⟨α, β, ⟨hα0, hβ0, hα, -, hαβ, -⟩, hE⟩ := H J hJ0 hcop
  have hαL : algebraMap (𝓞 L) L α ≠ 0 := by simpa using hα0
  have hβL : algebraMap (𝓞 L) L β ≠ 0 := by simpa using hβ0
  have hcL : algebraMap (𝓞 L) L c ≠ 0 := by simpa using hc0
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L (c ^ h * β) / algebraMap (𝓞 L) L α)
    (div_ne_zero (by rw [map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hcL) hβL) hαL), ?_, fun w hw hd => ?_⟩
  · have hI : Ideal.span {c ^ h * β} = v.asIdeal ^ h * Ideal.span {α} := by
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hJ, mul_pow, mul_assoc, hE]
    have hne : FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L α) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.2 hαL
    apply mul_right_cancel₀ hne
    rw [Units.val_mk0, FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hαL,
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, hI,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  · have hle : 𝔮 ≤ w.asIdeal := Ideal.le_of_dvd hd
    have hαw : α ∉ w.asIdeal := fun hm => w.isPrime.ne_top (top_le_iff.1 (by
      rw [← Ideal.isCoprime_iff_sup_eq.1 hα]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hm) hle))
    have hp : c ^ h - 1 ∈ w.asIdeal := by
      have := sub_dvd_pow_sub_pow c 1 h
      rw [one_pow] at this
      obtain ⟨t, ht⟩ := this
      rw [ht]
      exact Ideal.mul_mem_right _ _ (hc3 w hw hd)
    have hm : c ^ h * β - α ∈ w.asIdeal := by
      have : c ^ h * β - α = (c ^ h - 1) * β - (α - β) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hp) (hle hαβ)
    rw [Units.val_mk0, div_sub_one hαL, ← map_sub, map_div₀,
      (w.valuation_eq_one_iff_notMem (K := L)).2 hαw, div_one]
    exact (w.valuation_lt_one_iff_mem (K := L) _).2 hm

end GlobalTheory.Mem.FieldsEx

end
end

