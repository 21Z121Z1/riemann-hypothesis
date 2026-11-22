import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0029
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ContinuousHermitianInnerSelf
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
open PositivityTheory.Rg.Rsw.L.LToS

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem fix_mul_left {e : AE D} {M : Mx D a a} (hM : e • (M - 1) = M - 1) (x : Mx D a b) :
    e • (mm M x - x) = mm M x - x := by
  have h : mm M x - x = (M - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul]
  rw [h, ← Matrix.smul_mul, hM]

theorem fix_add_mul {e : AE D} {y : Mx D b c} (hy : e • y = y) (x : Mx D a b) (z : Mx D a c) :
    e • (z + mm x y - z) = z + mm x y - z := by
  rw [add_sub_cancel_left]
  show e • (x * y) = x * y
  rw [← Matrix.mul_smul, hy]

theorem fix_mul_right {e : AE D} {g : Mx D b b} (hg : e • (g - 1) = g - 1) (x : Mx D a b) :
    e • (mm x g - x) = mm x g - x := by
  have h : mm x g - x = x * (g - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
  rw [h, ← Matrix.mul_smul, hg]

theorem hc_U (e : AE D) (M : Mx D a a) (z : Mx D a b × Mx D a c) :
    (mm M (e • z.1), mm M (e • z.2)) = (e • mm M z.1, e • mm M z.2) := by
  simp only [mm, Matrix.mul_smul]

theorem hc_S (e : AE D) (y : Mx D b c) (z : Mx D a b × Mx D a c) :
    (e • z.1, e • z.2 + mm (e • z.1) y) = (e • z.1, e • (z.2 + mm z.1 y)) := by
  simp only [mm, Matrix.smul_mul, smul_add]

theorem hc_C (e : AE D) (g : Mx D c c) (z : Mx D a b × Mx D a c) :
    (e • z.1, mm (e • z.2) g) = (e • z.1, e • mm z.2 g) := by
  simp only [mm, Matrix.smul_mul]

theorem continuous_addMul (y : Mx D b c) : Continuous fun z : Mx D a b × Mx D a c => z.2 + mm z.1 y :=
  continuous_snd.add (continuous_fst.matrix_mul continuous_const)

theorem measurable_S (y : Mx D b c) : Measurable fun z : Mx D a b × Mx D a c => (z.1, z.2 + mm z.1 y) :=
  (continuous_fst.prodMk (continuous_addMul y)).measurable

theorem continuous_mulR (M : Mx D c c) : Continuous fun z : Mx D a b × Mx D a c => mm z.2 M :=
  continuous_snd.matrix_mul continuous_const

theorem measurable_C (M : Mx D c c) : Measurable fun z : Mx D a b × Mx D a c => (z.1, mm z.2 M) :=
  (continuous_fst.prodMk (continuous_mulR M)).measurable

theorem continuous_hermitian_inner_self (V : HSp D) : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1 := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.1 * (gA V * z.1)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem isOrb_e {V : HSp D} {b₀ : HermE D r} {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (hee : e * e = e ∧ cA D e = e) {ν : Measure (Mx D V.rank r × Mx D V.rank t)} (hν : IsOrb V b₀ 1 ν) :
    IsOrb V b₀ e ((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map fun z => (e • z.1, e • z.2)) := by
  have hA : MeasurableSet {z : Mx D V.rank r × Mx D V.rank t | IntOff S z.1 ∧ IntOff S z.2} :=
    (((isClosed_intOff S).preimage continuous_fst).inter ((isClosed_intOff S).preimage continuous_snd)).measurableSet
  have hf : Measurable fun z : Mx D V.rank r × Mx D V.rank t => (e • z.1, e • z.2) :=
    ((continuous_fst.const_smul e).prodMk (continuous_snd.const_smul e)).measurable
  have := hν.fin
  refine ⟨⟨fun K hK => ?_⟩, ?_, fun h hh => ?_, fun y hy => ?_, fun g hg => ?_⟩
  · obtain ⟨K', hK', hmem⟩ := boxP he hK
    rw [Measure.map_apply hf hK.measurableSet, Measure.restrict_apply (hf hK.measurableSet)]
    exact lt_of_le_of_lt (measure_mono fun z hz => hmem z hz.2.1 hz.2.2 hz.1) hK'.measure_lt_top
  · have hG : IsClosed {z : Mx D V.rank r × Mx D V.rank t |
        e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0} :=
      (isClosed_eq (continuous_fst.const_smul e) continuous_fst).inter
        ((isClosed_eq (continuous_snd.const_smul e) continuous_snd).inter
          ((isClosed_eq (continuous_hermitian_inner_self V) continuous_const).inter (isClosed_qv V b₀)))
    have hm : MeasurableSet {z : Mx D V.rank r × Mx D V.rank t |
        ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} := hG.isOpen_compl.measurableSet
    rw [Measure.map_apply hf hm]
    refine nonpos_iff_eq_zero.1 ?_
    refine (Measure.restrict_apply_le _ _).trans (le_of_eq (measure_mono_null (fun z hz => ?_) hν.supp))
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
    intro hg
    apply hz
    obtain ⟨-, -, h3, h4⟩ := hg
    refine ⟨by rw [smul_smul, hee.1], by rw [smul_smul, hee.1], ?_, ?_⟩
    · rw [ip_smul hee, h3, one_smul]
    · rw [qv_smul hee, h4, smul_zero]
  · have hφ : Measurable fun z : Mx D V.rank r × Mx D V.rank t => (mm (mt V h) z.1, mm (mt V h) z.2) :=
      ((continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)).measurable
    have key := map_transport (κ := 1) hA hf hφ hφ ?_ (fun z => hc_U e (mt V h) z)
      (by rw [one_smul]; exact hν.invU h (one_smul _ _))
    · rwa [one_smul] at key
    · ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [intOff_iff he (fix_mul_left hh z.1), intOff_iff he (fix_mul_left hh z.2)]
  · have key := map_transport (κ := 1) hA hf (measurable_S y) (measurable_S y) ?_
      (fun z => hc_S e y z)
      (by rw [one_smul]; exact hν.invS y (one_smul _ _))
    · rwa [one_smul] at key
    · ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [intOff_iff he (fix_add_mul hy z.1 z.2)]
  · exact map_transport hA hf (measurable_C (a := V.rank) (b := r) g.1) (measurable_C (a := V.rank) (b := r) g.1)
      (by
        ext z
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [intOff_iff he (fix_mul_right hg z.2)])
      (fun z => hc_C e g.1 z) (hν.cov g (one_smul _ _))

theorem toS_of (hI : IdemEx) : ToS := by
  classical
  intro D r t V b₀ _
  obtain ⟨S₁, h₁⟩ := exists_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS e he ν hν => ⟨isOrb_e he ((hI D S).2 e he) hν, fun z hz1 hz2 =>
    ⟨?_, yv_smul ((hI D S).2 e he) V b₀ z⟩⟩⟩
  show IntOff S (mm (rat b₀.1⁻¹) (mm (adj z.1) (mm (gA V) z.2)))
  exact intOff_mul (h₁ S (Finset.union_subset_left hS))
    (intOff_mul (intOff_adj hz1) (intOff_mul (h₂ S (Finset.union_subset_right hS)) hz2))

end PositivityTheory.Rg.Rsw.L.LToS

namespace PositivityTheory.Rg.Rsw.L

theorem toS : IdemEx → ToS := LToS.toS_of

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixTh
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

open LFixTh

open Classical in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem fixTh : IdemEx → GenG → GenK → FixTh := by
  intro _ hG hK D ρ p m ψ hψ χ hχ θ _ b₀ hb₀
  obtain ⟨S₁, hS₁⟩ := hK D p
  obtain ⟨S₃, hS₃⟩ := LFixW.psi_kernel hψ
  obtain ⟨S₄, hS₄⟩ := LFixW.ft_supp b₀.1 hb₀ hψ
  have hgood := eventually_goodPl hχ b₀
  refine ⟨S₁ ∪ S₃ ∪ S₄ ∪ (Filter.eventually_cofinite.1 hgood).toFinset, fun S hS e he Ω hΩ hgoodΩ => ?_⟩
  have hSg : ∀ v ∉ S, GoodPl χ b₀ v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)))
  have hSI := hS₃ S (fun v hv => hS (by simp [hv]))
  have hS4 := hS₄ S (fun v hv => hS (by simp [hv])) e he p m.μ
  have : m.μ.IsAddHaarMeasure := m.hμ.1
  let A' : Set (G D p) := {x | Ω x = Ω 1}
  have hA'c : IsClosed A' := by
    have e : A' = ⋂ y, {x | Ω x y = Ω 1 y} := by
      ext x; simp only [A', Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq (hΩ.cont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have hgen : ∀ g ∈ KOff D p S, (IsN g ∨ IsM g ∨ ∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D p S ∧ g = w * u * w⁻¹) →
      ∀ x ∈ A', g * x ∈ A' := by
    intro g hg hgt x hx
    simp only [A', Set.mem_ofPred_eq] at hx ⊢
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | ⟨w, u, hw, ⟨b, hb⟩, hu, rfl⟩
    · funext y
      rw [hΩ.unip g b hb x y, hx]
      by_cases hy : IntOff S y
      · rw [unip_one hSg hSI hg hb hy, one_mul]
      · rw [hgoodΩ y, if_neg hy, mul_zero]
    · have hbl := levi_blocks hg ha
      obtain ⟨h1, h2⟩ := levi_chr hχ hSg a (fun i j w => ((hbl i j).1 w).1) (fun i j v hv => ((hbl i j).2.1 v hv).1)
        (fun i j v hv => (hbl i j).2.2 v hv)
      funext y
      rw [hΩ.levi g a ha x y, hx, h1, h2, levi_good he hg ha _ hgoodΩ y]
      simp [npow]
    · let c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D)))) ((ρ : ℂ) / 2)
      have hΦ : ∀ y, Ω (w⁻¹ * x) y = ∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ := by
        intro y
        have e1 : w⁻¹ * x = w * ((w * w)⁻¹ * x) := by group
        rw [e1, hΩ.weyl w hw]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hΩ.levi _ (-1) (mat_ww hw) x z, hx, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
      have hzero : ∀ y, ψ (halfTr (b * pr b₀ y y).trace) * Ω (w⁻¹ * x) y = Ω (w⁻¹ * x) y := by
        intro y
        by_cases hy : IntOff S y
        · rw [unip_one hSg hSI hu hb hy, one_mul]
        · rw [hΦ y, show (∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ) = 0 from
            hS4 this _ (good_neg hgoodΩ c) y hy, mul_zero]
      funext y
      have e2 : w * u * w⁻¹ * x = w * (u * (w⁻¹ * x)) := by group
      have e3 : Ω 1 y = Ω (w * (w⁻¹ * x)) y := by rw [mul_inv_cancel_left, hx]
      rw [e2, e3, hΩ.weyl w hw, hΩ.weyl w hw]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      rw [hΩ.unip u b hb, hzero z]
  have hK' : (KOff D p S : Set (G D p)) ⊆ A' :=
    hS₁ S (fun v hv => hS (by simp [hv])) A' hA'c rfl hgen
  intro u hu h
  let A : Set (G D p) := {h | Ω (h * u) = Ω h}
  have hAc : IsClosed A := by
    have e : A = ⋂ y, {h | Ω (h * u) y = Ω h y} := by
      ext x; simp only [A, Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq
      (hΩ.cont.comp ((continuous_mul_const u).prodMk continuous_const))
      (hΩ.cont.comp (continuous_id.prodMk continuous_const))
  have h1 : (1 : G D p) ∈ A := by
    show Ω (1 * u) = Ω 1
    rw [one_mul]; exact hK' hu
  have hA := hG D p A hAc h1 fun g hgt x hx => by
    show Ω (g * x * u) = Ω (g * x)
    have hx' : Ω (x * u) = Ω x := hx
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | hw
    · funext y; rw [mul_assoc, hΩ.unip g b hb, hΩ.unip g b hb, hx']
    · funext y; rw [mul_assoc, hΩ.levi g a ha, hΩ.levi g a ha, hx']
    · funext y; rw [mul_assoc, hΩ.weyl g hw, hΩ.weyl g hw, hx']
  have hh : h ∈ A := hA ▸ Set.mem_univ h
  exact hh

end PositivityTheory.Rg.Rsw.L

end
end

