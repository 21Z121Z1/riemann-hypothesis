import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlab
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SlabCover

open IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

theorem exists_int_approx (m : ℕ) (hm : 0 < m) (y : Af F)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, ∃ t : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) ∧
      y - algebraMap F (Af F) (r : F) = (m : Af F) * t := by
  have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  set g : Af F → Af F := fun x => algebraMap F (Af F) (m : F)⁻¹ * (x - y) with hg
  have hgc : Continuous g := continuous_const.mul (continuous_id.sub continuous_const)
  set U : Set (Af F) := g ⁻¹' {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} with hU
  have hUo : IsOpen U :=
    (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hgc
  have hyU : y ∈ U := by
    intro v
    simp only [hg, sub_self, mul_zero]
    exact zero_mem _
  obtain ⟨ρ, hρ⟩ := (PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)).exists_mem_open hUo ⟨y, hyU⟩
  have hmm : (m : Af F) * algebraMap F (Af F) (m : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, mul_inv_cancel₀ hm', map_one]
  have he : algebraMap F (Af F) ρ = y + (m : Af F) * g (algebraMap F (Af F) ρ) := by
    simp only [hg, ← mul_assoc, hmm, one_mul]; ring
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (algebraMap F (Af F) ρ) v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [he]
    show y v + (m : v.adicCompletion F) * (g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact add_mem (hy v) (mul_mem (natCast_mem _ m) (hρ v))
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ρ
    (fun v => by
      have h := hint v
      rw [mem_adicCompletionIntegers] at h
      exact (valuedAdicCompletion_eq_valuation' v ρ).symm.trans_le h)
  refine ⟨r, -g (algebraMap F (Af F) ρ), fun v => ?_, ?_⟩
  · show -(g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact neg_mem (hρ v)
  · have : ((r : 𝓞 F) : F) = ρ := hr
    rw [this]
    conv_lhs => rw [he]
    ring

theorem exists_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ r : 𝓞 F, ∃ ρ ∈ S, ∃ q : 𝓞 F, (r : F) - ρ = (m : F) * (q : F) := by
  set b := RingOfIntegers.basis F
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  refine ⟨(Fintype.piFinset fun _ : ι => Finset.range m).image
    (fun c => (((∑ k, (c k : ℤ) • b k : 𝓞 F)) : F)), ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
      ← Module.finrank_eq_card_basis b, RingOfIntegers.rank]
  · intro r
    have hmz : (0 : ℤ) < m := by exact_mod_cast hm
    refine ⟨_, Finset.mem_image.2 ⟨fun k => ((b.repr r k) % m).toNat, ?_, rfl⟩,
      ∑ k, ((b.repr r k) / m) • b k, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (b.repr r k) hmz.ne'
      have h2 := Int.emod_lt_of_pos (b.repr r k) hmz
      omega
    · have hc : ∀ k, (((b.repr r k) % m).toNat : ℤ) = (b.repr r k) % m := fun k =>
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))
      have key : r - ∑ k, (((b.repr r k) % m).toNat : ℤ) • b k = (m : 𝓞 F) * ∑ k, ((b.repr r k) / m) • b k := by
        have hr := b.sum_repr r
        set a := b.repr r
        simp only [hc, Finset.mul_sum]
        conv_lhs => rw [← hr, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h := Int.emod_add_mul_ediv (a k) m
        have h' : ((a k % m : ℤ) : 𝓞 F) + (m : 𝓞 F) * ((a k / m : ℤ) : 𝓞 F) = ((a k : ℤ) : 𝓞 F) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 F)) h
        simp only [zsmul_eq_mul]
        linear_combination (-(b k)) * h'
      have := congrArg (fun x : 𝓞 F => (x : F)) key
      simpa using this

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay.SlabCover

variable {F : Type} [Field F] [NumberField F]

theorem exists_finite_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ y : Af F,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) →
      ∃ ρ ∈ S, ∃ z : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), z v ∈ v.adicCompletionIntegers F) ∧
        y - algebraMap F (Af F) ρ = (m : Af F) * z := by
  obtain ⟨S, hS, hres⟩ := exists_residues (F := F) m hm
  refine ⟨S, hS, fun y hy => ?_⟩
  obtain ⟨r, t, ht, hrt⟩ := exists_int_approx m hm y hy
  obtain ⟨ρ, hρS, q, hq⟩ := hres r
  refine ⟨ρ, hρS, t + algebraMap F (Af F) (q : F), fun v => ?_, ?_⟩
  · show t v + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F q) ∈ v.adicCompletionIntegers F
    exact add_mem (ht v) (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v q)
  · have e : algebraMap F (Af F) ρ = algebraMap F (Af F) (r : F) - (m : Af F) * algebraMap F (Af F) (q : F) := by
      rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, ← map_sub, ← hq]; ring_nf
    rw [e, mul_add, ← hrt]; ring

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay

open GlobalTheory.ArchDecay.SlabCover

theorem slab_subset_and_cover : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℕ, ∀ m : ℕ, 0 < m →
    slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧ (∀ r ∈ R, arch F r = 0) ∧
      ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m := by
  intro F _ _ κ _
  refine ⟨Module.finrank ℚ F * Fintype.card κ, fun m hm => ⟨?_, ?_⟩⟩
  · intro w hw i
    obtain ⟨a, ha0, hai, hae⟩ := hw i
    refine ⟨(m : AF F) * a, ?_, fun v => ?_, ?_⟩
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F ((m : Ainf F) * a.1) = 0
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 = 0 := ha0
      rw [map_mul, this, mul_zero]
    · show ((m : AF F) * a).2 v ∈ v.adicCompletionIntegers F
      show (m : v.adicCompletion F) * a.2 v ∈ v.adicCompletionIntegers F
      exact mul_mem (natCast_mem _ m) (hai v)
    · rw [hae, Nat.cast_one, one_mul]
  · obtain ⟨S, hS, hres⟩ := exists_finite_residues (F := F) m hm
    let emb : (κ → F) → (κ → AF F) := fun f i => pairA F 0 (algebraMap F (Af F) (f i))
    refine ⟨(Fintype.piFinset fun _ : κ => S).image emb, ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, pow_mul]
      exact Nat.pow_le_pow_left hS _
    · intro r hr
      obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hr
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    · intro w hw
      have hw' := hw
      choose a ha0 hai hae using hw'
      have hy : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (a i).2 v ∈ v.adicCompletionIntegers F :=
        fun i v => hai i v
      choose ρ hρS z hz hρz using fun i => hres (a i).2 (hy i)
      refine ⟨emb ρ, Finset.mem_image.2 ⟨ρ, Fintype.mem_piFinset.2 hρS, rfl⟩, ?_⟩
      have harch : arch F (emb ρ) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have hout : archOut F κ (w - emb ρ) = archOut F κ w := by
        rw [map_sub, archOut_apply F κ (emb ρ), harch, map_zero, sub_zero]
      intro i
      refine ⟨pairA F 0 (z i), map_zero _, fun v => hz i v, ?_⟩
      have h1 : (a i).1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1 = 0 := ha0 i
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      have h2 : (w - archIn F κ (archOut F κ w)) i = a i := by rw [hae i, Nat.cast_one, one_mul]
      rw [hout]
      have h3 : (w - emb ρ - archIn F κ (archOut F κ w)) i = (w - archIn F κ (archOut F κ w)) i - emb ρ i := by
        simp only [Pi.sub_apply]; abel
      rw [h3, h2]
      refine Prod.ext ?_ ?_
      · show (a i).1 - 0 = (m : Ainf F) * 0
        rw [h1, sub_zero, mul_zero]
      · show (a i).2 - algebraMap F (Af F) (ρ i) = (m : Af F) * z i
        exact hρz i

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFinite
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

def intFin : Set (Af F) := {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

theorem isOpen_intFin : IsOpen (intFin F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ => Valued.isOpen_valuationSubring _)

theorem isCompact_intFin : IsCompact (intFin F) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem sub_archIn_apply (w : κ → AF F) (i : κ) :
    (w - archIn F κ (archOut F κ w)) i = ((0 : Ainf F), (w i).2) := by
  have h : archIn F κ (archOut F κ w) i = infAd F (evI F (w i)) := by
    rw [archIn_apply, archOut_apply, LinearEquiv.symm_apply_apply]; rfl
  rw [Pi.sub_apply, h]
  refine Prod.ext ?_ ?_
  · change (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1) = 0
    rw [RingEquiv.symm_apply_apply, sub_self]
  · change (w i).2 - 0 = (w i).2
    rw [sub_zero]

theorem mem_slab_iff (m : ℕ) (hm : 0 < m) (w : κ → AF F) :
    w ∈ slab F κ m ↔ ∀ i, algebraMap F (Af F) ((m : F)⁻¹) * (w i).2 ∈ intFin F := by
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hc : algebraMap F (Af F) ((m : F)⁻¹) * (m : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, inv_mul_cancel₀ hm0, map_one]
  change (∀ i, ∃ a : AF F, _ ∧ _ ∧ _) ↔ _
  refine forall_congr' fun i => ?_
  rw [sub_archIn_apply]
  constructor
  · rintro ⟨a, -, ha, he⟩
    have h2 : (w i).2 = (m : Af F) * a.2 := by
      have := congrArg Prod.snd he
      rw [this]
      change sndA F ((m : AF F) * a) = _
      rw [map_mul, map_natCast]; rfl
    intro v
    rw [h2, ← mul_assoc, hc, one_mul]
    exact ha v
  · intro h
    refine ⟨pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2), ?_, fun v => h v, ?_⟩
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 = 0
      exact map_zero _
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = fstA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul]
        change (0 : Ainf F) = fstA F (m : AF F) * 0
        rw [mul_zero]
      · change (w i).2 = sndA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul, map_natCast]
        change (w i).2 = (m : Af F) * (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2)
        rw [← mul_assoc, mul_comm (m : Af F), hc, one_mul]

theorem isOpen_slab (m : ℕ) (hm : 0 < m) : IsOpen (slab F κ m) := by
  have : slab F κ m = ⋂ i, (fun w : κ → AF F => algebraMap F (Af F) ((m : F)⁻¹) * (w i).2) ⁻¹' intFin F := by
    ext w; rw [mem_slab_iff F κ m hm]; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_intFin F).preimage
    (continuous_const.mul (continuous_snd.comp (continuous_apply i)))

theorem archIn_mem_slab (t : Fin (dimA F κ) → ℝ) : archIn F κ t ∈ slab F κ 1 := by
  rw [mem_slab_iff F κ 1 one_pos]
  intro i v
  have : (archIn F κ t i).2 = 0 := rfl
  rw [this, mul_zero]
  exact zero_mem _

open scoped Pointwise in
theorem slab_open_cube_pos_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧ ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ := by
  intro F _ _ κ _
  refine ⟨fun m hm => isOpen_slab F κ m hm, fun μ hμ => ?_⟩
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  refine ⟨?_, fun A hA => ?_⟩
  · let U := archOut F κ ⁻¹' (Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1) ∩ slab F κ 1
    have hU : IsOpen U :=
      ((isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage (continuous_archOut F κ)).inter
        (isOpen_slab F κ 1 one_pos)
    have hne : U.Nonempty := by
      refine ⟨archIn F κ (fun _ => 1 / 2), ?_, archIn_mem_slab F κ _⟩
      simp only [Set.mem_preimage, archOut_archIn, Set.mem_pi, Set.mem_univ, true_implies]
      intro _; constructor <;> norm_num
    refine lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono ?_)
    exact Set.inter_subset_inter_left _ (Set.preimage_mono (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self))
  · let K : Set (κ → AF F) := (fun y : κ → Af F => fun i => pairA F 0 (y i)) '' Set.univ.pi fun _ => intFin F
    have hK : IsCompact K := by
      refine (isCompact_univ_pi fun _ => isCompact_intFin F).image (continuous_pi fun i => ?_)
      exact (continuous_const.prodMk (continuous_apply i) : Continuous fun y : κ → Af F => ((0 : Ainf F), y i))
    have hsub : archOut F κ ⁻¹' A ∩ slab F κ 1 ⊆ archIn F κ '' A + K := by
      rintro w ⟨hwA, hw⟩
      refine Set.mem_add.2 ⟨archIn F κ (archOut F κ w), ⟨_, hwA, rfl⟩, w - archIn F κ (archOut F κ w),
        ⟨fun i => (w i).2, fun i _ => ?_, funext fun i => (sub_archIn_apply F κ w i).symm⟩, add_sub_cancel _ _⟩
      have h := (mem_slab_iff F κ 1 one_pos w).1 hw i
      rwa [Nat.cast_one, inv_one, map_one, one_mul] at h
    exact ((measure_mono hsub).trans_lt ((hA.image (continuous_archIn F κ)).add hK).measure_lt_top).ne

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFrames
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SympFrames

def sgn {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal (sgn (p := p) (q := q)) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply, sgn] <;> split_ifs <;> simp

theorem lineSign_eq {p q r s : ℕ} (x : Ix p q) (y : Ix r s) : lineSign x y = sgn x * sgn y := by
  rcases x with x | x <;> rcases y with y | y <;> simp [lineSign, sgn]

theorem trace_jm {p q r s : ℕ} (c c' : Matrix (Ix p q) (Ix r s) ℂ) :
    (cᵀ * Jm p q * c'.map star * (Jm r s)ᵀ).trace = ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.diagonal_transpose, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, lineSign_eq, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem quad_eq_trace {α β : Type} [Fintype α] [Fintype β]
    (U U' : Matrix α β ℂ) (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, U i j * X i k * Y j l * star (U' k l) = (Uᵀ * X * U'.map star * Yᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frame_trace {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ}
    (X : Matrix α α ℂ) (Y : Matrix β β ℂ) (a b : ℂ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (hA : Aᵀ * (a • X) * A.map star = Jm P Q) (hC : Cᵀ * (b • Y) * C.map star = Jm R S)
    (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    a * b * ((A * c * Cᵀ)ᵀ * X * (A * c' * Cᵀ).map star * Yᵀ).trace =
      ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [← trace_jm, ← hA, ← hC]
  have hm : (A * c' * Cᵀ).map star = A.map star * c'.map star * (C.map star)ᵀ := by
    rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [hm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm C]
  simp only [Matrix.mul_assoc]
  ring

theorem symp_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (AE F E)) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, quad_eq_trace]
    exact frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelRankDegreeShareLeStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F), IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d := by
  first | exact @GlobalTheory.HSCore.share_le | exact GlobalTheory.HSCore.share_le | (intros; apply GlobalTheory.HSCore.share_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaVectorIsVacuumEvenRanks
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

theorem inter_congr_al {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α α' : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V)
    (F : V → ℂ) (h : ∀ x ∈ Λ₂, α x = α' x) : inter H α Λ₁ Λ₂ F = inter H α' Λ₁ Λ₂ F := by
  funext z
  unfold inter
  congr 1
  exact finsum_congr fun c => by rw [h _ (Quotient.out c : Λ₂).2]

theorem thetaVectorUpToUnits_thZero_of_even : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' →
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := by
  intro D cc δ B _ _ hcc hδ _ N N' hN hN'
  obtain ⟨n, hn⟩ := hN
  obtain ⟨n', hn'⟩ := hN'
  obtain rfl : N = n * 2 := by omega
  obtain rfl : N' = n' * 2 := by omega
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  refine ⟨bas B n n', B.kappa ^ (n' * n), GlobalTheory.T.orthonormalBasis_blockVacuumLatticeBasisFamily D cc δ B n n', GlobalTheory.T.kappaProduct_pow_algebraicModulusOneAll D cc δ B _, ?_⟩
  funext z
  obtain ⟨hsc', hF0', hidx', hprod⟩ := GlobalTheory.T.latticeIntertwiner_prod_orthogonal_blocks B.L B.ω₀ B.cq (Fin n' × Fin n) (Fin 4 × D.what₂.Tau)
    (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) hS.betaSemi
    (product_theta_mem B.L B.ω₀ _ hS.per hS.half _ hS.betaStd).1.2 hS.idx₁
  have hH : IsHerm (stdH B.L (Ix D n n')) := (standardFormBasic B.L _).2.1
  have hnat := GlobalTheory.T.latticeIntertwiner_comap_linear_isometry _ _ (formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau (n * 2) (n' * 2))
    (stdH B.L (Ix D n n')) (phi B n n') (fun x y => GlobalTheory.T.blockVacuumCoordinateEquiv_isometry D cc δ B n n' x y) hH _ _ _ _ hsc' hF0' hidx' z
  rw [GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels D cc δ B hS n n' z]
  congr 1
  rw [Iop_eq, GlobalTheory.T.blockVacuumLattice_eq_comap_standardLattice, GlobalTheory.T.la_tor0_stdL_eq_blkLat, show StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.tor0 D cc δ).abelian₂ (B.ω₀ / 2))
      = fun v => F0 B.L B.ω₀ (Ix D n n') (phi B n n' v) from funext (GlobalTheory.T.pullback_basis_theta_eq_F0_form D cc δ B n n')]
  rw [inter_congr_al _ _ (fun v => alphaQ B.cq (stdH B.L (Ix D n n')) (phi B n n' v)) _ _ _ ?_, hnat, hprod]
  · rfl
  · intro x hx
    have hx' : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) := by
      rw [GlobalTheory.T.la_tor0_stdL_eq_blkLat D cc δ B n n']; exact hx
    obtain ⟨m, hm⟩ := B.qInt0 hS (n * 2) (n' * 2) x hx'
    rw [al_eq D _ x m hm]
    unfold alphaQ qOf
    rw [← GlobalTheory.T.blockVacuumCoordinateEquiv_isometry D cc δ B n n' x x]
    rfl

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiInvariantTestFunctionSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bi_invariant_test_function_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 := by
  first | (exact @GlobalTheory.LKDef.Regroup.regroup) | (exact GlobalTheory.LKDef.Regroup.regroup) | (intros; apply GlobalTheory.LKDef.Regroup.regroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitaryStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  first | exact @GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers | exact GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers <;> assumption)
end

