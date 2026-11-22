import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0897
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0899
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnit
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut Module

noncomputable section

namespace GlobalTheory.CutCoreUnit

variable {D : D7} (i : D.nd.Loc)

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  rw [ccOff, ccAt, Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨f, hf, h0, rfl⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    change (⟨f, hf⟩ : D.nd.T i) ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    funext y
    exact h0 y.1 trivial y.2
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.1, f.2, fun x _ hx => ?_, rfl⟩
    change f ∈ RingHom.ker _ at hf
    rw [RingHom.mem_ker] at hf
    exact congrFun hf ⟨x, hx⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  intro hA D i r ρ π S hr hS hZ hN hU hSv hQ hl hsel hsha
  classical
  have hπ : π ∈ (Set.univ : Set (D.nd.X i)) := trivial
  obtain ⟨L, hL⟩ := CutCore.exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (CutCore.length_quot_eq_zero_iff.mp hL)
  have hd : lenQ i (del51 D.nd S S.π') = 0 :=
    CutCore.length_quot_eq_zero_iff.mpr hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)

  have hρ : Module.length (D.nd.O i) ↥(cocRho i r S Set.univ) ≤ (s : ℕ∞) := by
    obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Set.univ _ (WpO D.nd i ρ π) (cocRho i r S Set.univ) 0
      (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).1⟩)
    rw [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hlen
    refine hlen.trans ((GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).1) hfin ?_).trans ?_)
    · intro v h1 h2 h3
      exact CutCore.resIne_eq_bot_of_le i hC
        (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ S.ψρ (CutCore.inR'_one i r S) hU v h1 h2 h3)
    · have hc := (CutCore.lenCob_mono i _ hC).trans (GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).1
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc
      rw [hc, zero_add, ← hs]

  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
          else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ)) +
        ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) := by
    intro c
    obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 (cocChi i r S Set.univ c) (D.nd.Q i)
    have hZ1 := hC'.trans ((GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).2 c)
    have hunr : ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C' v = ⊥ := by
      intro v h1
      by_cases h3 : v ∈ D.nd.Q i
      · exact hq v h3
      refine CutCore.resIne_eq_bot_of_le i hC' ?_
      by_cases h2 : v ∈ D.nd.S i
      · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
        · have h := GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ v (Or.inl h2) hqd c
          rw [lenQ, CutCore.length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
          exact Submodule.subsingleton_iff_eq_bot.mp h
        · exact GlobalTheory.T.inertia_restriction_polynomial_condition_second_form D i r ρ π Set.univ S hr hS hπ v h2 hp c
      · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ _ (CutCore.inR'_one i r S) hU v h1 h2 h3
    refine hlen'.trans (add_le_add ?_ (Finset.sum_le_sum fun q hq' =>
      GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ q (Or.inr hq') (hQ q hq').1 c))
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc]
      have e : (c : ℕ) + 1 = 1 := by omega
      rw [e] at hZ1
      have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∀ f ∈ C',
          InCut i r Set.univ (chiRatO D.nd i 1) w hw f := by
        intro w hw f hf
        have h := (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf)
        rwa [e] at h
      refine GlobalTheory.UnramHom.length_le_classNumber hA D i C' hZ1 fun v => ?_
      by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
      · exact GlobalTheory.CutTrivIne.main D i C' v hv fun f hf =>
          (Submodule.span_le.mpr fun z hz => (hl v hv).2.2 z hz) (hloc v hv f hf)
      · exact hunr v hv
    · rw [if_neg hc]
      have h2 : 2 ≤ (c : ℕ) + 1 := by omega
      have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
      have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C' hZ1 h2 ht
        (fun f hf w hw => (Submodule.span_le.mpr fun z hz =>
          (hl w hw).2.1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) z hz)
            ((GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf))) hunr
      rw [Nat.add_sub_cancel] at h
      have hc0 := (CutCore.lenCob_mono i _ hC').trans ((GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).2 c)
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc0
      rw [hc0, zero_add] at h
      exact h

  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := CutCore.exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hχ' : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      ((L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q : ℕ) : ℕ∞) := by
    intro c
    refine (hχ c).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, hL]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  have htot := (GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound D i r ρ π Set.univ S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ' c))
  rw [← Nat.cast_sum, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  have hsum : ∑ c : Fin D.R.t, (L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q) =
      L * (h + ∑ e ∈ Finset.Ioo 0 D.R.t, g e) + D.R.t * ∑ q ∈ D.nd.Q i, z q := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, CutCore.sum_fin_ite ht, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hnat
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  show lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤ _
  rw [← ccOff_univ, hsp, hsh, hzq, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Set.univ π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat ⊢
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat ⊢
  have hq : (a : ℚ) ≤ ((s + (L * (h + G) + D.R.t * Z) : ℕ) : ℚ) := Nat.cast_le.mpr hnat
  push_cast at hq
  rw [div_le_iff₀ hLq]
  have e : ((s : ℚ) / L + G + (h : ℚ) + (D.R.t : ℚ) * ((Z : ℚ) / L)) * L =
      s + G * L + h * L + D.R.t * Z := by
    field_simp
  rw [e]
  nlinarith [hq]

end GlobalTheory.CutCoreUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPointMultiplicityLeRankProof
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.MultiplicityBound

theorem finrank_biSup_indep {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {t : ι → Submodule K V} (ht : iSupIndep t) (A : Finset ι) :
    Module.finrank K ↥(⨆ σ ∈ A, t σ) = ∑ σ ∈ A, Module.finrank K ↥(t σ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hs : (⨆ σ ∈ insert a A, t σ) = t a ⊔ ⨆ σ ∈ A, t σ := by
      rw [Finset.iSup_insert]
    have hd : Disjoint (t a) (⨆ σ ∈ A, t σ) := ht.disjoint_biSup (by simpa using ha)
    rw [hs, ← Submodule.finrank_sup_add_finrank_inf_eq, hd.eq_bot, finrank_bot, add_zero]

open Classical in

noncomputable def goodRows (D : D7) (i : D.nd.Loc) : Finset D.what₂.FT :=
  Finset.univ.filter (fun σ => D.nd.goodRow σ ∧ AtM D.nd D.naut i σ)

theorem dM_eq_sum (D : D7) (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (j : ℕ) (h : D.nd.j i = j) :
    dM D.nd D.naut i = ∑ σ ∈ goodRows D i, Module.finrank ℂ ↥(D.what₂.isot j σ) := by
  classical
  subst h
  have hr := D.nd.j_range i
  have hind : iSupIndep (D.what₂.isot (D.nd.j i)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have hsup : goodPartM D.nd D.naut i = ⨆ σ ∈ goodRows D i, D.what₂.isot (D.nd.j i) σ := by
    unfold goodPartM goodRows
    apply iSup_congr
    intro σ
    simp
  unfold dM
  rw [hsup]
  exact finrank_biSup_indep hind _

theorem sum_mult_le (D : D7) (hZ : SumRepresentations.ConclusionZ D) (i : D.nd.Loc) :
    (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (dM D.nd D.naut i : ℝ) := by
  classical
  rcases (D.nd.Zgood i).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  · have hG : HG D.nd D.naut i := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, (D.Zgood_tie i x).1 hx⟩
    have h3 := (hZ i hG).2.2
    rw [← h3, ← Nat.cast_sum]
    apply le_of_eq
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (D.nd.Zgood i))]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos ((D.Zgood_tie i x).1 hx)]
    · intro x _ hx
      rw [if_neg (fun h => hx ((D.Zgood_tie i x).2 h))]

end GlobalTheory.MultiplicityBound

open GlobalTheory.MultiplicityBound in

theorem GlobalTheory.NLink.multLe_of_rank : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ →
    KillingConditions.LocalisationUniqueness D → MultLe L := by
  intro D L h42 hZ hI h2 j hj w hw
  classical
  rcases (D.nd.locs j w).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  obtain ⟨hj0, hw0⟩ := (D.nd.locs_mem j w i0).1 hi0
  subst hj0 hw0
  have hr := D.nd.j_range i0
  have hind : iSupIndep (D.what₂.isot (D.nd.j i0)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have h1 : (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤
      ((∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => sum_mult_le D hZ i)
  refine h1.trans ?_
  apply Nat.cast_le.2
  have hdisj : (↑(D.nd.locs (D.nd.j i0) (D.nd.w i0)) : Set D.nd.Loc).PairwiseDisjoint (goodRows D) := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσ hσ'
    have hi := (D.nd.locs_mem _ _ i).1 hi
    have hi' := (D.nd.locs_mem _ _ i').1 hi'
    simp only [goodRows, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hσ'
    have htw : TwistedPlaces.TwLoc D i := by
      unfold TwistedPlaces.TwLoc
      rw [hi.2]
      exact hw
    exact hne (h2 i i' htw (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm) σ hσ.1 hσ.2 hσ'.2)
  calc (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i)
      = ∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ σ ∈ goodRows D i,
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        Finset.sum_congr rfl (fun i hi => dM_eq_sum D hI i _ ((D.nd.locs_mem _ _ i).1 hi).1)
    _ = ∑ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        (Finset.sum_biUnion hdisj).symm
    _ = Module.finrank ℂ ↥(⨆ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          D.what₂.isot (D.nd.j i0) σ) :=
        (finrank_biSup_indep hind _).symm
    _ ≤ Module.finrank ℂ (D.what₂.Mj (D.nd.j i0)) := Submodule.finrank_le _
    _ = L.zeroSpaceRankAtPlace (D.nd.j i0) (D.nd.w i0) := by
        unfold SizeData₂.zeroSpaceRankAtPlace Rows.Data.Zj
        rw [← D.nd.mu_w i0,
          LinearMap.finrank_range_of_inj (Formalism.MainNotions.J.theta_injective_of_scalars D h42 hI i0 hj)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageConditionsOfRankPart
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.AdmissibleSetting

theorem main : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), GlobalTheory.NFacts.Facts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  intro D L nch i r π ρ fa _ _ _ hr _ _
  exact ⟨Formalism.MainNotions.N.galois_condition_one_of D i r fa.Conclusion1.1 hr, Formalism.MainNotions.N.continuous_family_of D i r hr,
    Formalism.MainNotions.N.semisimple_family_of D i r hr⟩

end GlobalTheory.AdmissibleSetting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialKillsPotentiallyCrystallineModu
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct

namespace GlobalTheory.KillLocal

theorem actPow {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    actVB PD ρ (g ^ n) x = (actVB PD ρ g ^ n) x := by
  induction n generalizing x with
  | zero =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, map_mul, AlgEquiv.mul_apply]
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

theorem sumAeval {O LL M : Type} [CommRing O] [Field LL] [AddCommGroup M] [Module LL M] (f : O →+* LL)
    (T : Module.End LL M) (p : O[X]) (x : M) :
    ∑ n ∈ Finset.range (p.natDegree + 1), f (p.coeff n) • (T ^ n) x = Polynomial.aeval T (p.map f) x := by
  rw [Polynomial.aeval_eq_sum_range' (n := p.natDegree + 1) (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Polynomial.coeff_map]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → ∀ p : (D.nd.O i)[X], p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))), ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e (σ ^ n)) d = 0 := by
  intro D i w hw K' h hN hF hS m r hr hpc σ hσ p hp d hd
  have hPst := GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hr hpc
  obtain ⟨LL', hL, hV', hchar⟩ := GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement D i w hw m r hPst
  have hq := hchar σ hσ p hp
  have hkill := GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ hV' ⟨(σ : GE D.nd), hσ⟩ _ hq
  have hinj : Function.Injective (GlobalTheory.PstLine.incV hL m) := by
    intro x y hxy
    funext j
    exact (IntermediateField.inclusion hL).injective (congrFun hxy j)
  have hd' := GlobalTheory.T.aeval_kills_potCrystalline_of_kills_potSemistable (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL LL' h hN hF hS hL _ _ (GlobalTheory.PstLine.incV hL m) hinj (GlobalTheory.PstLine.isMor_incV (D.nbr i w hw) hL m _) _ (p.map (D.nbr i w hw).toLL) hkill d hd
  have hg : GlobalTheory.Pst.weilToGK (D.nbr i w hw) (D.nd.plOm.2 w) (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) = (D.nbr i w hw).e σ := rfl
  have key : ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • ((actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e σ)) ^ n) d = 0 := by
    rw [sumAeval]
    exact hd'
  refine (Finset.sum_congr rfl fun n _ => ?_).trans key
  have e1 : (D.nbr i w hw).e (σ ^ n) = (D.nbr i w hw).e σ ^ n := map_pow _ σ n
  exact congrArg _ ((congrArg (fun g => actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) g d) e1).trans (actPow _ _ _ _ _))

end GlobalTheory.KillLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntire
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.DiffInt

theorem integral_absDet_cpow_entire : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  intro E _ _ _ a μ S hS hμS c hc hδ F hF C hC
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδdef
  have hδc : Continuous δ := GlobalTheory.RSThetaLow.continuous_absDet
  have hae : ∀ᵐ g ∂(μ.restrict S), g ∈ S := ae_restrict_mem₀ hS
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  have key := GlobalTheory.integral_mul_cpow_of_rapid_decay_entire (GA E a) (μ.restrict S) δ F hδc.measurable
    (hae.mono fun g hg => ⟨lt_of_lt_of_le hc (hδ g hg).1, (hδ g hg).2⟩)
    (by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hδc.aestronglyMeasurable ?_
      refine hae.mono fun g hg => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hc.le (hδ g hg).1)]
      exact (hδ g hg).2)
    hF.aestronglyMeasurable
    (by
      intro K
      refine ⟨max C 0 / c ^ K, hae.mono fun g hg => ?_⟩
      have hcK : 0 < c ^ K := pow_pos hc K
      have h1 : c ^ K ≤ δ g ^ K := pow_le_pow_left₀ hc.le (hδ g hg).1 K
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      calc ‖F g‖ * c ^ K ≤ max C 0 * c ^ K :=
            mul_le_mul_of_nonneg_right ((hC g).trans (le_max_left _ _)) hcK.le
        _ ≤ max C 0 * δ g ^ K := mul_le_mul_of_nonneg_left h1 (le_max_right _ _))
  have := key.2.comp (differentiable_id.sub_const (1 : ℂ))
  exact this

end GlobalTheory.DiffInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageMulInvariantContinuousStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  first | (exact @GlobalTheory.GoodMul.good_mul_invariant) | (exact GlobalTheory.GoodMul.good_mul_invariant) | (intros; apply GlobalTheory.GoodMul.good_mul_invariant  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAverStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  first | (exact @GlobalTheory.CuspGeneric.good_top) | (exact GlobalTheory.CuspGeneric.good_top) | (intros; apply GlobalTheory.CuspGeneric.good_top  <;> assumption)
end

