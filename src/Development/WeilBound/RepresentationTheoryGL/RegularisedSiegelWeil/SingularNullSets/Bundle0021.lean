import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0020
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0753

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.AddMemIffOfZero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_iff_of_zero {X : Type} [AddCommGroup X] {P : Set X} (h0 : (0 : X) ∈ P) {a b : X} (hab : a = 0 ∨ b = 0) :
    a + b ∈ P ↔ a ∈ P ∧ b ∈ P := by
  rcases hab with h | h <;> subst h <;> simp [h0]

theorem box_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : sndA F (h + y) ∈ boxA S' U ↔ sndA F h ∈ boxA S' U ∧ sndA F y ∈ boxA S' U := by
  have hz : ∀ v, h.2 v = 0 ∨ y.2 v = 0 := fun v => by
    by_cases hv : v ∈ S
    · exact Or.inr (ker_snd hε hy hv)
    · exact Or.inl (fix_snd hε hh hv)
  have hadd : ∀ v, (sndA F (h + y)) v = h.2 v + y.2 v := fun v => rfl
  simp only [boxA, Set.mem_ofPred_eq, hadd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).1,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).1⟩,
      ⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).2,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun v hv => (add_mem_iff_of_zero (hU v) (hz v)).2 ⟨h1 v hv, h3 v hv⟩,
      fun v hv => (add_mem_iff_of_zero (zero_mem _) (hz v)).2 ⟨h2 v hv, h4 v hv⟩⟩

def tR (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : ℝ :=
  ρ (fstA F y) * (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem testT_eq (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : testT ρ S U y = ((tR ρ S U y : ℝ) : ℂ) := by
  simp only [testT, tR, Set.indicator]
  split_ifs <;> simp

theorem tR_nonneg {ρ : Ainf F → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : 0 ≤ tR ρ S U y :=
  mul_nonneg (hρ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

def bR (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℝ :=
  (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem tR_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε) (ρ : Ainf F → ℝ)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : tR ρ S' U (h + y) = tR ρ S' U h * bR S' U y := by
  have hf : fstA F (h + y) = fstA F h := by
    rw [map_add, fst_eq y, ker_fst hε hy, add_zero]
  have hb := box_split hSS hε U hU hh hy
  unfold tR bR
  rw [hf]
  by_cases h1 : sndA F h ∈ boxA S' U <;> by_cases h2 : sndA F y ∈ boxA S' U
  · rw [Set.indicator_of_mem (hb.2 ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h2 (hb.1 h').2), Set.indicator_of_notMem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem small_eventually {ι A M : Type} [Finite ι] [TopologicalSpace A] [Zero A] [TopologicalSpace M]
    (R : (ι → A) → M) (hR : Continuous R) (U : Set M) (hU : IsOpen U) (h0 : R 0 ∈ U) (Sp : ℕ → Set A)
    (hSp : Tendsto Sp atTop (𝓝 0).smallSets) : ∀ᶠ k in atTop, ∀ w : ι → A, (∀ i, w i ∈ Sp k) → R w ∈ U := by
  have hW : R ⁻¹' U ∈ 𝓝 (0 : ι → A) := hR.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, tt, htt, hsub⟩ := hW
  have hN : (⋂ i, tt i) ∈ 𝓝 (0 : A) := Filter.iInter_mem.mpr htt
  filter_upwards [tendsto_smallSets_iff.mp hSp _ hN] with k hk w hw
  exact hsub (fun i _ => Set.mem_iInter.mp (hk (hw i)) i)

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem approxId_of (h1 : OneD) : ApproxId := by
  classical
  intro D t ψ hψ S e he lam hlam
  have hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_eq_succ (n := 1) hCM.2.2.1
  have : BorelSpace (AF D.host.F) := ⟨rfl⟩
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  obtain ⟨eA, heA⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  obtain ⟨-, hBd⟩ := GlobalTheory.T.coordinate_form_symmetric_nondegenerate D.host.F D.host.E D.sp.cm.sig hCM _ (Module.finBasis D.host.F D.host.E) t
  have hpair := GlobalTheory.T.hermitian_pairing_in_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  generalize Module.finBasis D.host.F D.host.E = b at heA hBd hpair
  have hε0 : IsIdF S ((1, LIdemEx.indS S) : AF D.host.F) := ⟨rfl, fun v => rfl⟩
  obtain ⟨ε, hε, heS⟩ : ∃ ε : AF D.host.F, IsIdF S ε ∧ e = algebraMap (AF D.host.F) (AE D) ε :=
    ⟨_, hε0, e_eq D S e he⟩
  have hcA : cA D e = e := (LIdemEx.idem_props S e he).2
  obtain ⟨Θ, hΘ⟩ := exTheta' D t e ε heS hcA b eA heA
  have hcl : IsClosed ((fixE ε : AddSubgroup (AF D.host.F)) : Set (AF D.host.F)) :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have : LocallyCompactSpace (fixE ε) := hcl.locallyCompactSpace
  have : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨g1, G1, Sp, hg, hlim, hsupp, hSp⟩ := h1 D.host.F hCM.1 ψ hψ S ε hε (Measure.addHaar) inferInstance
  obtain ⟨c, -, hTr⟩ := transfer Θ lam (Measure.addHaar : Measure (fixE ε))
  set Bm := (coordForm D.sp.cm.sig b t).map (algebraMap D.host.F (AF D.host.F)) with hBm
  let sT : Mx D t t → _ := fun T => if hT : T ∈ hermA D t then
    Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hT⟩ else 0
  refine ⟨fun k x => ∏ i, g1 k (Θ x i), fun k T => if T ∈ hermA D t then (c : ℝ) * ∏ i, G1 k (sT T i) else 0,
    fun k => ⟨?_, ?_, fun T hT => ⟨?_, ?_⟩⟩, fun x => ?_, ?_⟩
  · exact (hTr (fun _ => g1 k)).2 (fun _ => (hg k).1)
  · intro x
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => (hg k).2.1 _)
  · beta_reduce
    rw [if_pos hT]
    exact mul_nonneg c.2 (Finset.prod_nonneg fun i _ => ((hg k).2.2 _).1)
  · beta_reduce
    have hpt : ∀ x : hermS D t e, pch ψ x.1.1 T = ∏ i, ψ ((Θ x i).1 * sT T i) := by
      intro x
      rw [pch_eq D t ψ x.1.1 T x.1.2 hT, hpair, dotProduct, char_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [sT, dif_pos hT, hΘ, heA]
    calc ∫ x, (∏ i, g1 k (Θ x i)) * pch ψ x.1.1 T ∂lam
        = ∫ x, ∏ i, (fun i h => g1 k h * ψ (h.1 * sT T i)) i (Θ x i) ∂lam := by
          congr 1; funext x; rw [hpt, ← Finset.prod_mul_distrib]
      _ = (c : ℂ) * ∏ i, ∫ h, g1 k h * ψ (h.1 * sT T i) ∂(Measure.addHaar : Measure (fixE ε)) :=
          (hTr (fun i h => g1 k h * ψ (h.1 * sT T i))).1
      _ = _ := by
          rw [if_pos hT]
          push_cast
          congr 1
          exact Finset.prod_congr rfl fun i _ => ((hg k).2.2 _).2
  · have := tendsto_finsetProd Finset.univ (fun i _ => hlim (Θ x i))
    simpa using this
  · intro C hC hCT ε' hε'
    have hunit : IsUnit Bm.det := by
      have h := (RingHom.map_det (algebraMap D.host.F (AF D.host.F)) (coordForm D.sp.cm.sig b t)).symm
      rw [hBm]
      exact h ▸ (isUnit_iff_ne_zero.mpr hBd).map _
    let R : (Idx t (Module.finrank D.host.F D.host.E) → AF D.host.F) → Mx D t t := fun w => (eA.symm (Bm⁻¹ *ᵥ w)).1
    have hRc : Continuous R :=
      continuous_subtype_val.comp (eA.symm.continuous.comp (continuous_const.matrix_mulVec continuous_id))
    have hU : IsOpen {M : Mx D t t | -M ∉ C} := hC.isOpen_compl.preimage continuous_neg
    have h0 : R 0 ∈ {M : Mx D t t | -M ∉ C} := by
      have : R 0 = 0 := by simp [R, Matrix.mulVec_zero]
      simp only [Set.mem_ofPred_eq, this, neg_zero]
      exact fun h => (hCT 0 h).2.2 rfl
    filter_upwards [small_eventually R hRc _ hU h0 Sp hSp] with k hk T hTC
    obtain ⟨hTA, heT, -⟩ := hCT T hTC
    by_contra hlt
    have hpos := lt_trans hε' (not_le.mp hlt)
    beta_reduce at hpos
    rw [if_pos hTA] at hpos
    have hprod : ∀ i, G1 k (sT T i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hpos.ne') i (Finset.mem_univ i)
    have hfixT : ∀ i, ε * sT T i = sT T i := by
      intro i
      simp only [sT, dif_pos hTA, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, coord_fix D t e ε heS b _ heT j]
    have hw : ∀ i, -(sT T i) ∈ Sp k := fun i => by
      have := hsupp k (sT T i) (hprod i)
      rwa [hfixT] at this
    have hmem := hk (fun i => -(sT T i)) hw
    have hR : R (fun i => -(sT T i)) = -T := by
      have h2 : (fun i => -(sT T i)) = -(Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hTA⟩) := by
        funext i; simp only [sT, dif_pos hTA, Pi.neg_apply]
      simp only [R, h2, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
        map_neg, ← heA, eA.symm_apply_apply]
      rfl
    simp only [hR, neg_neg] at hmem
    exact hmem hTC

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

set_option maxHeartbeats 1600000 in
theorem cutId : Polar → CfFJ → CoefId → ThCoef → FourierPt → WeakApproximationFinitePlace → CfInv → ThBdd → CutLow → IkSch → IkEq → WMaj → CutId := by
  intro hPolar hCfFJ hCoefId hThCoef hFP hWA1 hCfInv hThBdd hCutLow _ hIkEq hWMaj
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb hnb v C hK hKv 𝓕 h𝓕 Ψ Ψ' hΨ hΨ'
  obtain ⟨nb₀, lam, 𝓖, hCD⟩ := GlobalTheory.T.coefficient_data_exists D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hCD.2⟩
  obtain ⟨κ, hκ⟩ := hCoefId D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb lam 𝓖 hC
  refine ⟨κ, ?_⟩

  have hBr : B.rank = W.rank + 2 * t := d.rank_add.symm
  have hlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) :=
    LCutId.law0 hS.hB Φ _ (by rw [hBr, ← hn]; push_cast; ring)
  have hηB : ResEta D χ B.rank := by rw [hBr]; exact LCutId.resEta_add hS.hη t
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hS.hψ χ hS.hχ hηB θ hS.hθ μB hS.hμB ωB hS.hB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hpol := hPolar D n W.rank t hn hS.big ψ hS.hψ χ hS.hχ hS.hη
    (fun h0 => absurd h0 (by have := hS.pos; omega)) θ hS.hθ H hH _ hφc hlaw U dd E σ hcont ε hrad
  have hRk := hpol.1 1 le_rfl

  obtain ⟨hcf, -, -⟩ := hCfFJ D n H _ _ U dd E σ hcont ε hrad
  have hcf1c := (hcf 1).1
  have hcf1i := (hcf 1).2
  have hcfK : ∀ k ∈ KAt D n v, ∀ g, cf dd E ((t : ℂ) / 2) ε 1 (g * k) = cf dd E ((t : ℂ) / 2) ε 1 g := by
    intro k hk g
    exact hCfInv D n H _ _ U dd E σ hcont ε hrad k (fun g => (hKv k hk).2 g) (fun g => by
      show (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0
      rw [map_mul, Module.End.mul_apply, (hKv k hk).1]) 1 g
  obtain ⟨-, ⟨U₁, hU₁, hU₁i⟩, hlow⟩ := hCutLow D n W.rank ψ hS.hψ nb hnb v C hK _ hcf1c hcf1i hcfK

  have hΨK : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ k, (hKv k hk).1, ← hΨ])
  obtain ⟨-, hthL, ⟨U₂, hU₂, hU₂i⟩, -, hthF⟩ :=
    hThBdd D n W ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μW hS.hμW ωW hS.hW nb hnb v C hK Ψ Ψ' hΨK hΨ'
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : G D n → ℂ, F₂ = fun g => ∫ h in 𝓕, theta ωW Ψ' g h ∂I.m := ⟨_, rfl⟩
  have hF₁L : ∀ γ ∈ GF D n, ∀ g, cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g := by
    intro γ hγ g
    unfold cutR
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hcf1i γ hγ]
  have hF₁c : Continuous (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) := by
    unfold cutR
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hcf1c.comp (continuous_mul_const _))
  have hF₂L : ∀ γ ∈ GF D n, ∀ g, F₂ (γ * g) = F₂ g := by
    intro γ hγ g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    exact hthL γ hγ g h
  have hF₂R : ∀ k ∈ U₂, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, F₂ (g * k) = F₂ g := by
    intro k hk hk' g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    show ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW (g * k) Ψ').1 _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW g Ψ').1 _
    rw [map_mul, Module.End.mul_apply, hU₂i k hk hk']

  have key : ∀ g, proj D.sp.cm.sig (Jst D n) v g = 1 → cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g = κ * F₂ g := by
    intro g hg
    obtain ⟨-, hTc, hTβ⟩ := hThCoef D n W ψ hS.hψ θ hS.hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hCD.2 (ωW g Ψ').1 (ωW g Ψ').2
    have hthS : ∀ x : hermA D n, F₂ (nb x * g) = thS W I.m 𝓕 (fun X => pch ψ x.1 (ip W X X) * (ωW g Ψ').1 X) := by
      intro x
      rw [hF₂]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      exact (hthF x g hg).2 h
    have hF₂c : Continuous fun x : hermA D n => F₂ (nb x * g) := by
      simp only [hthS]; exact hTc
    have hF₁c' : Continuous fun x : hermA D n => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) :=
      hF₁c.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)
    have hper : ∀ {F : G D n → ℂ}, (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
        ∀ γ ∈ ratHerm D n, ∀ x, F (nb (γ + x) * g) = F (nb x * g) := by
      intro F hF γ hγ x
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hF _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have hcoef : ∀ β : HermE D n, fc ψ lam 𝓖 nb (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) β g =
        κ * ∫ x in 𝓖, F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
      intro β
      simp only [hthS]
      have hlowβ := hlow lam 𝓖 hC β g hg
      have horb : ∀ x₀ : Matrix (Fin W.rank) (Fin n) D.host.E, gramQ W x₀ = β.1 →
          orb W I.m (ωW g Ψ').1 x₀ = cutF ψ C (rat β.1) * orb W I.m (ωW g Ψ).1 x₀ := by
        intro x₀ hx₀
        unfold orb
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        show (ωW g Ψ').1 _ = _ * (ωW g Ψ).1 _
        rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
      rcases lt_trichotomy β.1.rank W.rank with hlt | heq | hgt
      · rw [hlowβ.2 hlt]
        by_cases hx : ∃ x, x.rank = W.rank ∧ gramQ W x = β.1
        · obtain ⟨x₀, hx₀r, hx₀⟩ := hx
          rw [(hTβ β).2 x₀ hx₀r hx₀]
          unfold orb
          rw [show (∫ h, (ωW g Ψ').1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) ∂I.m) = ∫ _h, (0 : ℂ) ∂I.m from
            integral_congr_ae (Eventually.of_forall fun h => ?_), integral_zero, mul_zero]
          show (ωW g Ψ').1 _ = 0
          rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
          by_cases hdual : ∀ y : hermA D n, IntAt v y → pch ψ y.1 (rat β.1) = 1
          · rw [hK β hlt hdual, zero_mul]
          · push Not at hdual
            obtain ⟨y, hy, hne⟩ := hdual
            have hfix := LCutId.omega_fix hS.hW hnb Ψ hΨK hg hy (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀))
            rw [LCutId.ip_orbit, hx₀] at hfix
            have h2 : (1 - pch ψ y.1 (rat β.1)) * (ωW g Ψ).1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) = 0 := by
              rw [sub_mul, one_mul, ← hfix, sub_self]
            rw [(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]
        · rw [(hTβ β).1 hx, mul_zero]
      · rw [hlowβ.1]
        by_cases hx : ∃ x, gramQ W x = β.1
        · obtain ⟨x₀, hx₀⟩ := hx
          have hx₀r : x₀.rank = W.rank := by
            have h1 := LCutId.rank_gram_le W x₀
            rw [hx₀, heq] at h1
            exact le_antisymm (Matrix.rank_le_height x₀) h1
          rw [((hκ β heq g).2 x₀ hx₀), (hTβ β).2 x₀ hx₀r hx₀, horb x₀ hx₀,
            hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ g]
          ring
        · rw [(hκ β heq g).1 hx, (hTβ β).1 fun ⟨x, _, hx'⟩ => hx ⟨x, hx'⟩, mul_zero, mul_zero]
      · rw [hlowβ.1, hRk nb lam 𝓖 hC β (Nat.succ_le_of_lt hgt) g, mul_zero]
        rw [(hTβ β).1 fun ⟨x, hxr, hx'⟩ => by
          have h1 := LCutId.rank_gram_le W x
          rw [hx', hxr] at h1
          omega, mul_zero]
    have hf0 := hFP D n ψ hS.hψ lam 𝓖 hCD.2
      (fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g))
      (hF₁c'.sub (continuous_const.mul hF₂c))
      (fun γ hγ x => by simp only [hper hF₁L γ hγ x, hper hF₂L γ hγ x])
      (fun β => by
        have i1 := LCutId.intOn hCD.2 hF₁c' (hper hF₁L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have i2 := LCutId.intOn hCD.2 hF₂c (hper hF₂L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have e : (fun x : hermA D n => (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g)) *
            conj (pch ψ x.1 (rat β.1))) = fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) * conj (pch ψ x.1 (rat β.1)) -
              κ * (F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1))) := funext fun x => by ring
        rw [e, integral_sub i1 (i2.const_mul κ), integral_const_mul, ← LCutId.fc_eq hS.hψ, hcoef β, sub_self])
    have h0 := congrFun hf0 0
    simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
    exact sub_eq_zero.1 h0

  intro g
  obtain ⟨γ, hγ, g', hg', k, hkU, hkv, hgeq⟩ := hWA1 D n v (U₁ ⊓ U₂) (by rw [Subgroup.coe_inf]; exact hU₁.inter hU₂) g
  have e1 : cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g' * k) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g' := by
    rw [hU₁i k (Subgroup.mem_inf.1 hkU).1 hkv, hF₁L γ hγ]
  have e2 : F₂ (γ * g' * k) = F₂ g' := by
    rw [hF₂R k (Subgroup.mem_inf.1 hkU).2 hkv, hF₂L γ hγ]
  rw [hgeq, e1, key g' hg', ← e2, hF₂]

end PositivityTheory.Rg.Rsw.L

end
end

