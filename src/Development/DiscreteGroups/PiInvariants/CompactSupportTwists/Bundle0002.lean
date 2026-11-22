import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
section
set_option linter.all false

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_cV_eq (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ := by
  change ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v) (u.1 v)‖ = _
  exact (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _

theorem mult_eq_two (v : InfinitePlace E) : v.mult = 2 := by
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v)]

theorem logAbs_eq_log_ideleNorm (u : (Ad E)ˣ) :
    logAbs (u : Ad E) = Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm u) := by
  have hu : ∀ v, ‖cV v (u : Ad E)‖ ≠ 0 := fun v => norm_ne_zero_iff.2 (u.isUnit.map (cV v)).ne_zero
  have hw : ∀ w, ‖cW w (u : Ad E)‖ ≠ 0 := fun w => norm_ne_zero_iff.2 (u.isUnit.map (cW w)).ne_zero
  have hinf : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm u = ∏ v : InfinitePlace E, ‖cV v (u : Ad E)‖ ^ 2 := by
    change ∏ v : InfinitePlace E, _ = _
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [norm_cV_eq, mult_eq_two]
  have hfin : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm u = ∏ᶠ w : HeightOneSpectrum (𝓞 E), ‖cW w (u : Ad E)‖ := rfl
  have hs : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => ‖cW w (u : Ad E)‖).Finite :=
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finite_mulSupport (E := E) u
  have hsub : (Function.support fun w : HeightOneSpectrum (𝓞 E) => Real.log ‖cW w (u : Ad E)‖) ⊆
      (hs.toFinset : Set (HeightOneSpectrum (𝓞 E))) := fun w hw' => by
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_mulSupport, Function.mem_support] at hw' ⊢
    intro h1
    rw [h1, Real.log_one] at hw'
    exact hw' rfl
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm, MonoidHom.mul_apply, hinf, hfin,
    finprod_eq_prod_of_mulSupport_subset _ (s := hs.toFinset) (fun _ h => hs.mem_toFinset.2 h),
    Real.log_mul (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hu v))
      (Finset.prod_ne_zero_iff.2 fun w _ => hw w),
    Real.log_prod fun v _ => pow_ne_zero _ (hu v), Real.log_prod fun w _ => hw w, logAbs,
    finsum_eq_sum_of_support_subset _ hsub]

theorem continuous_logAbs_det : Continuous fun g : GA E n => logAbs g.val.det := by
  have e : (fun g : GA E n => logAbs g.val.det) =
      fun g => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (Matrix.GeneralLinearGroup.det g)) :=
    funext fun g => logAbs_eq_log_ideleNorm (Matrix.GeneralLinearGroup.det g)
  rw [e]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp Matrix.GeneralLinearGroup.continuous_det).log
    fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _

theorem continuous_ldet : Continuous (ldet : H E n 0 → ℝ) :=
  continuous_logAbs_det.comp continuous_fst

theorem continuous_of_mem (π : CuspSub E n) {ψ : Sm E n} (h : ψ ∈ π.V) : Continuous ψ.1 :=
  ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ h).1.level

end DiscreteGroups.T1.G
end
end

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosSt
section
noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

def PiClosureInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  ∀ (D : Dom E n 0) (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (ψ : ι → Sm E n) (u : ι → ℝ → ℂ)
  (z : H E n 0) (f : Hs (ι := ι) D), (∀ i, ψ i ∈ π.V ∧ Continuous (u i) ∧ HasCompactSupport (u i)) →
  (∀ i, (f i : H E n 0 → ℂ) =ᵐ[D.ν] fun x => (ψ i).1 (x * z).1 * u i (ldet (x * z))) → f ∈ piSp D π ι

end DiscreteGroups.T1.G

end
end

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitAll
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem one_lt_absNorm (w : HeightOneSpectrum (𝓞 E)) : 1 < Ideal.absNorm w.asIdeal := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact w.isPrime.ne_top
  omega

theorem norm_absC_val (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((GlobalTheory.CuspRep.Model.absC E (x : ℂ)).val w : ℂˣ) : ℂ)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-x) := by
  rw [PositivityTheory.Rg.Rs.StrStepB.absC_val]
  have h0 : 0 < (Ideal.absNorm w.asIdeal : ℕ) := by
    have := one_lt_absNorm w
    omega
  rw [Complex.norm_natCast_cpow_of_pos h0]
  simp

theorem speh_one {d : ℕ} (h : d = 1) (k : Fin d) : spehExp d k = 0 := by
  subst h
  simp [spehExp]

theorem sum_one {d : ℕ} (h : d = 1) (f : Fin d → Multiset ℂˣ) (k : Fin d) : ∑ i, f i = f k := by
  subst h
  exact Fintype.sum_eq_single k fun i hi => absurd (Subsingleton.elim i k) hi

theorem twist_zero {d a : ℕ} (h : d = 1) (k : Fin d) (P : CuspSub E a) :
    CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d k : ℝ) : ℂ))) = CG.mk P := by
  rw [speh_one h k, Complex.ofReal_zero, PositivityTheory.Rg.Rs.StrStepB.absC_zero, ← CG.twist_mk, CG.twist_one]

theorem hasSat_of_sigma {m n : ℕ} {X : CG E m} {Y : CG E n} (h : (⟨m, X⟩ : Σ k, CG E k) = ⟨n, Y⟩)
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (hX : X.HasSat w B) : Y.HasSat w B := by
  cases h
  exact hX

theorem d_eq_one {a d : ℕ} (P : CuspSub E a) (ha : 1 ≤ a) (hd : 1 ≤ d) (w : HeightOneSpectrum (𝓞 E))
    (b : Fin d → Multiset ℂˣ)
    (hb : ∀ k, (CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d k : ℝ) : ℂ)))).HasSat w (b k))
    (hn : ∀ k, ∀ z ∈ b k, ‖(z : ℂ)‖ = 1) : d = 1 := by
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hk0 : 0 < d := by omega
  have hk1 : d - 1 < d := by omega
  have e : CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨d - 1, hk1⟩ : ℝ) : ℂ))) =
      (CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)))).twist
        (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)) := by
    rw [CG.twist_mk, ← CuspSub.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add]
    congr 3
    push_cast
    ring
  have h1 := PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC
    (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨0, hk0⟩ : ℝ) : ℂ))) (hb ⟨0, hk0⟩)
    ((spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)
  rw [← e] at h1
  have hu := (hb ⟨d - 1, hk1⟩).unique h1
  obtain ⟨z, hz⟩ : ∃ z, z ∈ b ⟨0, hk0⟩ :=
    Multiset.card_pos_iff_exists_mem.mp (by rw [(hb ⟨0, hk0⟩).card]; omega)
  have hm : z * (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)).val w
      ∈ b ⟨d - 1, hk1⟩ := by
    rw [hu]
    exact Multiset.mem_map_of_mem _ hz
  have h2 := hn _ _ hm
  rw [Units.val_mul, norm_mul, hn _ z hz, one_mul, norm_absC_val] at h2
  have hx : spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ = 1 - (d : ℝ) := by
    simp only [spehExp]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hx] at h2
  have h3 : 1 < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(1 - (d : ℝ))) := by
    refine Real.one_lt_rpow (by exact_mod_cast one_lt_absNorm w) ?_
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  linarith

theorem split_freq (hC : SplitCore) {n : ℕ} (hn : 1 ≤ n) (π : CG E n) (hu : π.IsUnitary) (ht : Temp π) :
    ∃ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w := by
  show ¬ (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ¬ IsSplitAt w)
  intro h
  obtain ⟨j, -⟩ := hC E n hn π hu ht (Fin 0) (fun _ => 1) (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (h.mono fun w hw hs => absurd hs hw)
  exact j.elim0

theorem rSplitAll : RSplitAll := by
  intro hC hS hStr E _ _ _ n hn π hu ht D hD hL
  choose a d P ha hd hPu hPn hP using hStr E n D hD
  have hAsc : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hP i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have hSt : ∀ i, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ b : Fin (d i) → Multiset ℂˣ,
      (∀ k, (CG.mk ((P i).twist (GlobalTheory.CuspRep.Model.absC E ((spehExp (d i) k : ℝ) : ℂ)))).HasSat w (b k)) ∧
        GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) ∧ GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (∑ k, b k) :=
    fun i => hS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i) (D.discrete i) (hPu i) (hPn i) (hAsc i)
      (D.loc i) (fun k => GlobalTheory.CuspRep.Model.absC E ((spehExp (d i) k : ℝ) : ℂ))
      (fun k => PositivityTheory.Rg.Rs.InductionInStages.isAbsPow_absC _)
  have hAll := Filter.eventually_all.2 hSt
  have hF := split_freq hC hn (CG.mk π) hu ht
  have hd1 : ∀ i, d i = 1 := by
    intro i
    obtain ⟨w, hw, ⟨b, hb, -, hbs⟩, hl, ⟨B0, hB0, hB0n⟩⟩ := (hF.and_eventually ((hSt i).and (hL.and ht))).exists
    obtain ⟨B, ⟨b', hb', hsum⟩, hB⟩ := hl hw
    have e1 : b' i = ∑ k, b k := (hb' i).2.unique hbs
    have e2 : B0 = B := hB0.unique hB
    refine d_eq_one (P i) (ha i) (hd i) w b hb fun k z hz => hB0n z ?_
    rw [e2, ← hsum]
    exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, by rw [e1]; exact Multiset.mem_sum.2 ⟨k, Finset.mem_univ _, hz⟩⟩
  let k0 : ∀ i, Fin (d i) := fun i => ⟨0, by rw [hd1 i]; exact Nat.one_pos⟩
  have hsp : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : Fin D.c → Multiset ℂˣ, (∀ j, (CG.mk (P j)).HasSat w (b j)) ∧ (CG.mk π).HasSat w (∑ j, b j) := by
    refine (hAll.and hL).mono fun w hw hs => ?_
    obtain ⟨hst, hl⟩ := hw
    choose b hb _ hbs using hst
    obtain ⟨B, ⟨b', hb', hsum⟩, hB⟩ := hl hs
    have e : ∀ i, b' i = b i (k0 i) := fun i => ((hb' i).2.unique (hbs i)).trans (sum_one (hd1 i) (b i) (k0 i))
    refine ⟨fun i => b i (k0 i), fun i => ?_, ?_⟩
    · have h1 := hb i (k0 i)
      rwa [twist_zero (hd1 i) (k0 i) (P i)] at h1
    · have h2 : ∑ i, b i (k0 i) = B := by
        rw [← hsum]
        exact Finset.sum_congr rfl fun i _ => (e i).symm
      rw [h2]
      exact hB
  obtain ⟨j, hj⟩ := hC E n hn (CG.mk π) hu ht (Fin D.c) a (fun i => CG.mk (P i)) ha
    (fun i => (CG.isUnitary_mk _).2 (hPu i)) hsp
  have haj : a j = n := congrArg Sigma.fst hj
  have hN : ∀ i, D.N i = a i := fun i => by
    obtain ⟨h, -⟩ := hAsc i
    rw [← h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hd1 i, one_mul]
  have hone : ∀ i, i = j := by
    intro i
    by_contra hij
    have h2 : D.N i + D.N j ≤ ∑ k, D.N k := by
      rw [← Finset.sum_pair hij]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := D.pos i
    rw [D.h, hN j, haj] at h2
    omega
  refine hAll.mono fun w hst => ?_
  choose b hb hsph hbs using hst
  refine ⟨b j (k0 j), ⟨fun i => b i (k0 i), fun i => ⟨hsph i, ?_⟩, ?_⟩, ?_⟩
  · show GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (b i (k0 i))
    rw [← sum_one (hd1 i) (b i) (k0 i)]
    exact hbs i
  · exact Fintype.sum_eq_single j fun i hi => absurd (hone i) hi
  · have h1 := hb j (k0 j)
    rw [twist_zero (hd1 j) (k0 j) (P j)] at h1
    exact hasSat_of_sigma hj h1

end DiscreteGroups.T1.G

end
end

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ThetaAMulPhiU
section
noncomputable section

set_option linter.unusedSectionVars false

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair

namespace DiscreteGroups.T1.G

theorem map_PhiU {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (a : ℕ) :
    GeneralLinearGroup.map p (PhiU a R) = PhiU a S := by
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, apply_ite]
  split_ifs <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ratGL_PhiU : ratGL E n (PhiU n E) = PhiU n (Ad E) :=
  map_PhiU (algebraMap E (Ad E)) n

theorem PhiU_Ad : PhiU n (Ad E) = finGL E n (PhiU n (Af E)) * infGL E n (PhiU n (Cinf E)) := by
  conv_lhs => rw [← infGL_mul_finGL (PhiU n (Ad E))]
  rw [map_PhiU, map_PhiU, infGL_comm]

theorem thetaA_mul_PhiU (g : GA E n) :
    GlobalTheory.ThetaPull.thetaA E n g * PhiU n (Ad E) = PhiU n (Ad E) * PositivityTheory.Rg.BcB.thetaA E n g := by
  have e : invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) = PositivityTheory.Rg.BcB.thetaA E n g := by
    refine Units.ext ?_
    change ((GeneralLinearGroup.map (conjAd E) g)⁻¹ : GL (Fin n) (Ad E)).valᵀ =
      (((g⁻¹ : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ
    rw [← map_inv]
    rfl
  change MulAut.conj (PhiU n (Ad E)) (invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g)) * PhiU n (Ad E) = _
  rw [e, MulAut.conj_apply, inv_mul_cancel_right]

theorem thetaFixOf_of (hG : GlobalTheory.Published.GelfandKazhdanDual) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hM : GlobalTheory.Published.CuspidalMultiplicityOne) : PositivityTheory.Rg.BcB.Desc.ThetaFixOf := by
  intro E _ _ _ n _ π hd
  unfold PositivityTheory.Rg.BcB.Desc.ThetaFix
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired hF E n π (hG E n π) hd
  refine ⟨GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc, fun ψ hψ => ?_⟩
  obtain ⟨T, hT⟩ := hc
  have hiso : (GlobalTheory.ThetaPull.thetaSub π).Iso π := by
    refine ⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨χ, rfl⟩ := ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).surjective φ
    have e : (GlobalTheory.ThetaPull.thetaSub π).op o ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V χ) =
        (GlobalTheory.ThetaPull.pull E n).submoduleMap π.V (π.op (thetaOp o) χ) :=
      Subtype.ext (GlobalTheory.ThetaPull.act_pull o χ.1)
    change T (((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).symm ((GlobalTheory.ThetaPull.thetaSub π).op o
        ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V χ))) = π.op o (T (((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).symm
        ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V χ)))
    erw [e, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hT]
  have hV : (GlobalTheory.ThetaPull.thetaSub π).V = π.V := hM E n _ _ (Quotient.sound hiso)
  have hχ : act (.fin (PhiU n (Af E))) (act (.cpt (PhiK E n)) ψ) ∈ π.V := π.stable _ _ (π.stable _ _ hψ)
  have hp : GlobalTheory.ThetaPull.pull E n (act (.fin (PhiU n (Af E))) (act (.cpt (PhiK E n)) ψ)) ∈
      (GlobalTheory.ThetaPull.thetaSub π).V := Submodule.mem_map_of_mem hχ
  refine ⟨_, hV ▸ hp, fun g => ?_⟩
  have hK : Unitary.toUnits (PhiK E n) = PhiU n (Cinf E) := Units.ext rfl
  have h1 : (GlobalTheory.ThetaPull.pull E n (act (.fin (PhiU n (Af E))) (act (.cpt (PhiK E n)) ψ))).1 g =
      ψ.1 (GlobalTheory.ThetaPull.thetaA E n g * PhiU n (Ad E)) := by
    change ψ.1 (GlobalTheory.ThetaPull.thetaA E n g * finGL E n (PhiU n (Af E)) * infGL E n (Unitary.toUnits (PhiK E n))) = _
    rw [hK, mul_assoc, ← PhiU_Ad]
  rw [h1, thetaA_mul_PhiU, ← ratGL_PhiU]
  exact (π.cusp ψ hψ).1.left _ _

end DiscreteGroups.T1.G

end
end

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UncutHalf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def lInt0 {ι : Type} [Fintype ι] (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x : H E a b) : ℂ :=
  ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))

def IsPiPart {n : ℕ} {ι : Type} [Fintype ι] (D : Dom E n 0) (π : CuspSub E n)
    (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) : Prop :=
  (∀ f ∈ piSp D π ι, Uπ f = U f) ∧ ∀ f ∈ (piSp D π ι)ᗮ, Uπ f = 0

def KerSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (π : CuspSub E n)
  (ι : Type) [Fintype ι] (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D) (τ C : ℝ) (N : ℕ),
  (∀ V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, Integrable (lInt D k₁ k₂ τ V) D.ν ∧
    ‖∫ x, lInt D k₁ k₂ τ V x ∂D.ν‖ ≤ C * (1 + τ) ^ N * ‖V‖) →
  ∀ U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, (∀ f ∈ piSp D π ι, U f ∈ piSp D π ι) →
    (∀ f ∈ (piSp D π ι)ᗮ, U f ∈ (piSp D π ι)ᗮ) →
    ∃ Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, IsPiPart D π U Uπ ∧ ‖Uπ‖ ≤ ‖U‖ ∧
      ‖∫ x, lInt D k₁ k₂ τ U x ∂D.ν - ∫ x, lInt D k₁ k₂ τ Uπ x ∂D.ν‖ ≤
        C * (1 + τ) ^ N * ‖U ∘L (piSp D π ι)ᗮ.subtypeL‖

def UncutHalf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ →
  ∀ (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → IsTwTr D.μ π (trM Φ M) t →
    Integrable (lInt0 D k₁ k₂ Uπ) D.ν ∧ ∫ x, lInt0 D k₁ k₂ Uπ x ∂D.ν = t / 2

def DomOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] [MeasurableSpace (GA E 0)] [BorelSpace (GA E 0)]
  (μ₁ : Measure (GA E n)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E 0)) [μ₂.IsHaarMeasure], ∃ (F₁ : Set (GA E n))
  (F₂ : Set (GA E 0)) (D : Dom E n 0), IsFundamentalDomain (ratGL E n).range F₁ μ₁ ∧
    IsFundamentalDomain (ratGL E 0).range F₂ μ₂ ∧ (∀ τ φ, cutTrD D τ φ = PositivityTheory.Rg.BcB.cutTr2 μ₁ μ₂ F₁ F₂ τ φ) ∧
    ∀ F : H E n 0 → ℂ, Continuous F → HasCompactSupport F → ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂μ₂ ∂μ₁

end DiscreteGroups.T1.G

end
end

