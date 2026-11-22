import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

theorem continuous_family_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r := by
  intro x
  exact (hr x).1

theorem semisimple_family_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS (D := D) i r := by
  intro x W hW
  obtain ⟨W', hW', hc⟩ := (hr x).2.1 W hW
  exact ⟨W', hW', hc⟩

theorem coefficient_compatibility_of (D : D7) (i : D.nd.Loc)
    (hdeg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.DegW D.nbr i w hw) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility (D := D) i := by
  intro w hw
  exact ⟨(D.nbr i w hw).eO_alg, ⟨(D.nbr i w hw).eO_cont, (D.nbr i w hw).eO_symm_cont⟩, hdeg w hw⟩

theorem isOpen_ker_redRep (D : D7) (a : D.nd.Loc) {n : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin n) (D.nd.O a))
    (h : Continuous (fun g => ((ρ g : GL (Fin n) (D.nd.O a)) : Matrix (Fin n) (Fin n) (D.nd.O a)))) :
    IsOpen ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) := by
  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic a)).1 1
  have hset : ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) =
      ⋂ i, ⋂ j, (fun g => ((ρ g : GL (Fin n) (D.nd.O a)) : Matrix (Fin n) (Fin n) (D.nd.O a)) i j -
        (1 : Matrix (Fin n) (Fin n) (D.nd.O a)) i j) ⁻¹'
        ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage]
    rw [Units.ext_iff, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have h1 : ((1 : GL (Fin n) (IsLocalRing.ResidueField (D.nd.O a))) :
        Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (D.nd.O a))) i j =
        IsLocalRing.residue (D.nd.O a) ((1 : Matrix (Fin n) (Fin n) (D.nd.O a)) i j) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h1]
    exact Ideal.Quotient.eq
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact hm.preimage ((h.matrix_elem i j).sub continuous_const)

theorem charpoly_of_decomp (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) (g : GE D.nd) :
    (rO D.nd i r π g).charpoly = (rhoO D.nd i ρ π g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := by
  obtain ⟨e, he⟩ := hdec
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  show (mapM (toK D.nd i) (rO D.nd i r π) g).charpoly = (mapM (toK D.nd i) (rhoO D.nd i ρ π) g).charpoly *
    ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)))

  have hmat : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) (KK D.nd i)), (Matrix.toLin' M).charpoly = M.charpoly := by
    intro m M
    rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun (KK D.nd i) (Fin m)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

  have hconj : e.conj (Matrix.toLin' (mapM (toK D.nd i) (rO D.nd i r π) g)) =
      (Matrix.toLin' (mapM (toK D.nd i) (rhoO D.nd i ρ π) g)).prodMap
        (Matrix.toLin' (Matrix.diagonal fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    apply LinearMap.ext
    intro p
    obtain ⟨u, rfl⟩ := e.surjective p
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.toLin'_apply, LinearMap.prodMap_apply]
    rw [he g u]
    refine Prod.ext rfl (funext fun c => ?_)
    simp [Matrix.mulVec_diagonal]
  have hdiag : (Matrix.diagonal fun c : Fin D.R.t =>
      toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)).charpoly =
      ∏ c : Fin D.R.t, (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    have hch : Matrix.charmatrix (Matrix.diagonal fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) =
        Matrix.diagonal fun c : Fin D.R.t =>
          (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.charmatrix_apply]
      · simp [Matrix.charmatrix_apply, hab, Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.charpoly, hch, Matrix.det_diagonal]

  have hidx : ∏ c : Fin D.R.t, (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    rw [Fin.prod_univ_eq_prod_range (fun c => X - C (toK D.nd i ((chiU D.nd i (c + 1) g : (D.nd.O i)ˣ) : D.nd.O i))),
      Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun c => X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) 0 D.R.t 1]
    congr 1
  rw [← hmat, ← LinearEquiv.charpoly_conj e, hconj, LinearMap.charpoly_prodMap, hmat, hmat, hdiag, hidx]

def AbsIrreducibleDistinct (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x, AbsIrrDistinct (repK D.nd i r x)

theorem galois_condition_three_of (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h32 : Formalism.MainNotions.SumRepresentations.Conclusion41 D) (hr : GoodR D.nd i r)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))))
    (hHG : HG D.nd D.naut i) (hN9 : ResidualIrreducibleRankR D) (hB : LitBurnside (G D.host.E D.nd.Om))
    (hc : AbsIrreducibleDistinct D i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 (D := D) i r ρ π := by
  have h2 : ∀ x (g : GE D.nd), (mapM (IsLocalRing.residue (D.nd.O i)) (rO D.nd i r x) g).charpoly =
      (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t,
          (X - C (IsLocalRing.residue (D.nd.O i) ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    intro x g
    have e1 := (((h32 i).2.2 r hr).2.2.1).2 x π g
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_of_decomp D i r ρ π hdec g)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    refine e1.trans (e2.trans ?_)
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  refine ⟨hc, h2, ?_⟩
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i _ hcont, ?_⟩
    intro x w hw B σ hB' hσ
    rw [← (hr x).2.2 w hw B σ hB' hσ, ← Matrix.charpoly_map]
    exact (h2 x σ).symm
  have h3 := hB (D.nd.l i) D.R.r _ (hN9 i hHG _ hrb).1
  exact span_descent (D.naut.kFbar i) (fun g => mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g) h3

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

theorem LiftF_mono (F : LatHom L L') {e e' : ℕ} (he : e ≤ e') (h : F.LiftF PD e) : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (h c hc)

end Gen

section Fields

variable {l : ℕ} [Fact l.Prime]

theorem Ks_mono (K : FinExt l) {s s' : ℕ} (h : s ≤ s') : Ks K s ≤ Ks K s' := by
  unfold Formalism.BasicNotions.Loc.Ks
  refine sup_le_sup_left ?_ _
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  apply IntermediateField.subset_adjoin
  simp only [Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := pow_dvd_pow l h
  rw [hc, pow_mul, hx, one_pow]

theorem caseA_of_unram (P : LocPrime l) (H : LocHW l P) {K : FinExt l} {LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨RingHom.injective (algebraMap ↥(K0 K) ↥K.1), fun y =>
    ⟨⟨(y : Om l), IntermediateField.mem_inf.mpr ⟨y.2, hK y.2⟩⟩, by ext; rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p K]
  exact hl

end Fields

theorem Hmax_const_le (n M h : ℕ) : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => M) (fun _ => h) ≤ M + h := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  exact Finset.sup_le fun _ _ => le_rfl

def LiftWin (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (M h : ℕ) : Prop :=
  ∀ T : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL),
    IsSubquotOfSums T.ρ (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) →
    IsCrys (Br.PD D.loc D.nbr i w hw) T.ρ ∧
      ∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ τ (Set.Icc (-(M : ℤ)) h)

theorem lifting_condition_of_crystalline_lift (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (M h : ℕ) (CA CB CK : ℝ) (hCA : 0 ≤ CA)
    (h54 : Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK) (hl : D.nd.l i ≠ 2)
    (hur : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i))
    (hwin : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      ∀ C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw, C.IsGood → LiftWin D i r w hw C M h)
    (he : ∀ w ∈ dc.col, CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) ≤ (e' w : ℝ)) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LiftExponentAtPlaces (D := D) i r dc e' := by
  intro w hw hcol C hC

  have hgood : Good (D.nbr i w hw).Kw 1 C.LL := by
    refine ⟨le_rfl, fun h2 => absurd h2 hl, ?_, ?_⟩
    · unfold Formalism.BasicNotions.Loc.Ks Formalism.BasicNotions.Loc.K0
      exact le_sup_of_le_left (le_inf le_rfl (hur w hw hcol))
    · intro τ x
      obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits' τ (fun (y : Om (D.nd.l i)) =>
        ⟨(Algebra.IsIntegral.isIntegral (R := ℚ_[D.nd.l i]) (A := Om (D.nd.l i)) y).tower_top,
          by first | exact IsAlgClosed.splits _ | exact IsAlgClosed.splits_codomain' _ | exact IsAlgClosed.splits_of_splits _ | simp⟩)
      have e : φ x = τ x := by
        rw [← hφ]
        rfl
      rw [← e]
      have hle : Ks (D.nbr i w hw).Kw 1 ≤ C.LL.1.comap φ := by
        unfold Formalism.BasicNotions.Loc.Ks Formalism.BasicNotions.Loc.K0
        refine sup_le ?_ ?_
        · intro y hy
          show φ y ∈ C.LL.1
          exact C.le ((D.nbr i w hw).LL_split (φ.comp (D.nbr i w hw).Kw.1.val)
            ⟨y, (IntermediateField.mem_inf.mp hy).1⟩)
        · rw [IntermediateField.adjoin_le_iff]
          intro y hy
          show φ y ∈ C.LL.1
          apply hC
          have hy1 : y ^ D.nd.l i = 1 := by simpa using hy
          obtain ⟨c, hc⟩ := Nat.dvd_lcm_left (D.nd.l i) D.host.condN
          rw [← map_pow, hc, pow_mul, hy1, one_pow, map_one]
      exact hle x.2
  have hA : Formalism.MainNotions.LiftingTheory.CaseA ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) :=
    caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hgood (hur w hw hcol) hl
  unfold LiftAt
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 Fm hFm
  let T1 : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) := ⟨V1, ρ1, hc1, L1⟩
  let T2 : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) := ⟨V2, ρ2, hc2, L2⟩
  have hw1 := hwin w hw hcol C hC T1 hs1
  have hw2 := hwin w hw hcol C hC T2 hs2
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) T1 (fun _ => M) (fun _ => h) :=
    fun _ τ _ => hw1.2 τ
  have hSur : Formalism.MainNotions.LiftingTheory.Sur ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) (T₁ := T1) (T₂ := T2) Fm :=
    ⟨hw1.1, hw2.1, hFm⟩

  have hlift := h54.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hgood hA T1 T2 Fm (fun _ => M) (fun _ => h) hSur hJ
  have hbound := (h54.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hgood T1 (fun _ => M) (fun _ => h) hw1.1 hJ).1 hA
  rw [(D.loc (D.nd.l i)).PD_p] at hbound
  have hH := Hmax_const_le (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) M h
  have hl1 : (1 : ℝ) < D.nd.l i := by exact_mod_cast (D.nd.lPrime i).out.one_lt
  have hHr : (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h) : ℝ) ≤
      ((M + h : ℕ) : ℝ) := by exact_mod_cast hH
  have hlog : Real.logb (D.nd.l i)
      ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h) : ℝ) + 1) ≤
      Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)
  have hdiv : (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h) : ℝ) /
      (D.nd.l i : ℝ) ≤ ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) := by
    gcongr
  have hmono := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl (1 : ℝ)) hdiv) (add_le_add (le_refl (1 : ℝ)) hlog)) hCA
  have hle : Formalism.MainNotions.LiftingTheory.ePA (D.nd.l i)
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M))
      (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h))
      (Formalism.MainNotions.LiftingTheory.jumpSet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) T1
        (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M))
        (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => h))) ≤ e' w := by
    exact_mod_cast hbound.trans (hmono.trans (he w hcol))
  rw [(D.loc (D.nd.l i)).PD_p] at hlift
  exact LiftF_mono _ _ hle hlift

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualConditionOnLinkedSides
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

open scoped Pointwise

def GlobalDatumLocalisationCondition (D : D7) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (s : D.ntw.Sig i) k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k),
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ : G D.host.E D.nd.Om, Formalism.MainNotions.BlochKatoReduction.IsWild A σ → Formalism.MainNotions.BlochKatoReduction.Gen.rbar D.ntw i s σ = 1

def ValuationStabilityUnlinkedSides (D : D7) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s : D.ntw.Sig i, ¬ SideLoc D i (D.ntw.side i s) → Formalism.MainNotions.BlochKatoReduction.Gen.ValuationStabilityAtRing D.ntw i s

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem theorem_one_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.wachTheoremLocal D.loc HW D.locA F Cm := h.1

theorem consistency_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.consL D.loc HW D.locA F := h.2.1

theorem proposition_two_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.prop2L D.loc HW D.locA F := h.2.2.1

theorem lemma_three_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.wachLengthLocal D.loc HW D.locA F := h.2.2.2

theorem first_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p1L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).1

theorem second_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.1

theorem third_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p3L D.loc HW D.locA F Cm := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.1

theorem fourth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.1

theorem fifth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p5L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.1

theorem sixth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p6L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.1

theorem seventh_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p7L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.1

theorem eighth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p8L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.2.1

theorem delta_invariants_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p9L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.2.2.1

theorem tenth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p10L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.2.2.2

theorem second_first_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2aL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).1

theorem second_b_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2bL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).2.1

theorem second_c_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2cL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).2.2.1

theorem second_dual_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2dL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).2.2.2

theorem lifting_local_of_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionL D HW F := h.1

theorem wach_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionW D HW F := h.2.1

theorem lift_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK := h.2.2.2.2.2.2.2

end Formalism.MainNotions.N
end
end

