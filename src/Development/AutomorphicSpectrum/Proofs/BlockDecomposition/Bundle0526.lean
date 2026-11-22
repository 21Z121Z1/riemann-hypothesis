import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0045
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkFiber
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac PositivityTheory.Rg.BcB.F.Tail.BS
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem filt_zero (ϖ : kˣ) (x : Fin n → ℤ) : filt ϖ x 0 = nO k n := by
  have h : ∀ g : GL (Fin n) k, Deep ϖ x 0 g := fun g i j hij hd => by
    have := Fin.lt_def.1 hij; omega
  ext g
  exact ⟨fun hg => hg.1, fun hg => ⟨hg, h _, h _⟩⟩

theorem filt_succ_le (ϖ : kˣ) (x : Fin n → ℤ) (d : ℕ) : filt ϖ x (d + 1) ≤ filt ϖ x d :=
  fun _ hg => ⟨hg.1, fun i j hij hd => hg.2.1 i j hij (by omega), fun i j hij hd => hg.2.2 i j hij (by omega)⟩

theorem relIndex_filt_zero {ϖ : kˣ} (h1 : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    (filt ϖ x d).relIndex (nO k n) =
      Nat.card 𝓀[k] ^ ∑ e ∈ Finset.range d, ∑ p ∈ diagPairs n e, (x p.1 - x p.2).toNat := by
  induction d with
  | zero => rw [filt_zero]; simp
  | succ d ih =>
    have hle : ∀ e, filt ϖ x e ≤ nO k n := fun e _ hg => hg.1
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (filt_succ_le ϖ x d) (hle d), ih, GlobalTheory.T.filtration_relIndex_eq_residue_card_pow k n ϖ h1 x hx d,
      Finset.sum_range_succ, pow_add, mul_comm]

theorem mk_fiber {ϖ : kˣ} (h1 : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {m m' : GL (Fin n) k}
    (hm : m ∈ nO k n) (hm' : m' ∈ nO k n) :
    (QuotientGroup.mk (m * tor ϖ x) : GL (Fin n) k ⧸ iwahori k (Fin n)) = QuotientGroup.mk (m' * tor ϖ x) ↔
      m⁻¹ * m' ∈ filt ϖ x n := by
  have hnorm : (tor ϖ x)⁻¹ ∈ Subgroup.normalizer ((unipB k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
    inv_mem ((GlobalTheory.CompanionTheory.IwahoriDatumGL.iwahoriCass k n).norm_N _ ⟨_, rfl⟩)
  have e : (m * tor ϖ x)⁻¹ * (m' * tor ϖ x) = (tor ϖ x)⁻¹ * (m⁻¹ * m') * (tor ϖ x)⁻¹⁻¹ := by group
  rw [QuotientGroup.eq, e, GlobalTheory.T.filtration_eq_conj_nilpotent_integral k n ϖ h1 x hx]
  have hy : m⁻¹ * m' ∈ nO k n := mul_mem (inv_mem hm) hm'
  constructor
  · intro h
    refine ⟨_, ⟨h, (Subgroup.mem_normalizer_iff.1 hnorm _).1 hy.2⟩, ?_⟩
    simp [MulAut.conj_apply]
    group
  · rintro ⟨z, hz, e'⟩
    have : (tor ϖ x)⁻¹ * (m⁻¹ * m') * (tor ϖ x)⁻¹⁻¹ = z := by
      rw [← e']
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hz.1

theorem jacHk : JacHk := by
  intro k _ _ _ _ n V _ _ π _ ϖ h1 x hx u hu
  have hfix : ∀ b ∈ iwahori k (Fin n), π b u = u := fun b hb => GlobalTheory.IwahoriInj.mem_fixed.1 hu b hb
  set I := iwahori k (Fin n) with hI
  set t : GL (Fin n) k := tor ϖ x with ht
  set w : Jacquet π (unipB k (Fin n)) := Submodule.Quotient.mk (π t u) with hw
  let F : nO k n → GL (Fin n) k ⧸ I := fun m => QuotientGroup.mk (m.1 * t)
  have hval : ∀ m ∈ nO k n, ∀ b ∈ I, (Submodule.Quotient.mk (π (m * t * b) u) : Jacquet π (unipB k (Fin n))) = w := by
    intro m hm b hb
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix b hb, hw, Submodule.Quotient.eq]
    exact GlobalTheory.IwahoriInj.sub_mem_twKer hm.2 _
  let f : GL (Fin n) k → ℂ := fun g => if ∃ a ∈ I, ∃ b ∈ I, g = a * t * b then (1 : ℂ) else 0

  have hsupp : ∀ q : GL (Fin n) k ⧸ I, (∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b) ↔ q ∈ Set.range F := by
    intro q
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      obtain ⟨m, hm, c, hc, e2⟩ := GlobalTheory.T.iwahori_double_coset_torus_nilpotent k n ϖ h1 x hx a ha b hb
      rw [← ht] at e2
      refine ⟨⟨m, hm⟩, ?_⟩
      rw [← QuotientGroup.out_eq' q, e, e2]
      refine QuotientGroup.eq.2 ?_
      simpa [mul_assoc] using inv_mem hc
    · rintro ⟨m, rfl⟩
      have : (F m).out⁻¹ * (m.1 * t) ∈ I := QuotientGroup.eq.1 (QuotientGroup.out_eq' (F m))
      refine ⟨m.1, m.2.1, (m.1 * t)⁻¹ * (F m).out, ?_, by group⟩
      simpa using inv_mem this

  have hcard : Nat.card (Set.range F) = (filt ϖ x n).relIndex (nO k n) := by
    let Φ : (nO k n ⧸ (filt ϖ x n).subgroupOf (nO k n)) → Set.range F := fun c =>
      Quotient.liftOn' c (fun m => (⟨F m, m, rfl⟩ : Set.range F)) (fun a b hab => Subtype.ext
        ((mk_fiber h1 hx a.2 b.2).2 (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hab))))
    have hΦ : Function.Bijective Φ := by
      constructor
      · intro c c'
        refine Quotient.inductionOn₂' c c' fun a b e => ?_
        exact Quotient.sound' (QuotientGroup.leftRel_apply.2 (Subgroup.mem_subgroupOf.2
          ((mk_fiber h1 hx a.2 b.2).1 (congrArg Subtype.val e))))
      · rintro ⟨_, m, rfl⟩
        exact ⟨Quotient.mk'' m, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
  have hq : Nat.card 𝓀[k] ≠ 0 := Nat.card_pos.ne'
  have hcard' := hcard.trans (relIndex_filt_zero h1 hx n)
  have hQ : (Set.range F).Finite := by
    have : Finite (Set.range F) := Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ hq)
    exact Set.toFinite _
  have hs : (Function.support fun q : GL (Fin n) k ⧸ I => f q.out • π q.out u).Finite := by
    refine hQ.subset fun q hq' => (hsupp q).1 ?_
    by_contra h
    exact hq' (by simp only [f, if_neg h, zero_smul])
  have e2 : ∀ q : GL (Fin n) k ⧸ I, (twKer π (unipB k (Fin n)) 1).mkQ.toAddMonoidHom (f q.out • π q.out u) =
      if q ∈ Set.range F then w else 0 := by
    intro q
    by_cases h : q ∈ Set.range F
    · obtain ⟨m, hm⟩ := id h
      have hb : (m.1 * t)⁻¹ * q.out ∈ I :=
        QuotientGroup.eq.1 ((show (QuotientGroup.mk (m.1 * t) : GL (Fin n) k ⧸ I) = q from hm).trans
          (QuotientGroup.out_eq' q).symm)
      have e : m.1 * t * ((m.1 * t)⁻¹ * q.out) = q.out := by group
      have hp : ∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b := ⟨m.1, m.2.1, _, hb, e.symm⟩
      have := hval m.1 m.2 _ hb
      rw [e] at this
      simp only [f, if_pos hp, if_pos h, one_smul]
      exact this
    · have : ¬ ∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b := fun h' => h ((hsupp q).1 h')
      simp only [f, if_neg this, if_neg h, zero_smul, map_zero]
  have e1 : (Submodule.Quotient.mk (hkS π I f u) : Jacquet π (unipB k (Fin n))) =
      ∑ᶠ q : GL (Fin n) k ⧸ I, if q ∈ Set.range F then w else 0 := by
    rw [← finsum_congr e2]
    exact AddMonoidHom.map_finsum (twKer π (unipB k (Fin n)) 1).mkQ.toAddMonoidHom hs
  have e3 : (∑ᶠ q : GL (Fin n) k ⧸ I, if q ∈ Set.range F then w else 0) = Nat.card (Set.range F) • w := by
    rw [finsum_eq_sum_of_support_subset (s := hQ.toFinset) _ (fun q hq' => by
      simp only [Set.Finite.coe_toFinset]
      by_contra h
      exact hq' (by simp only [if_neg h]))]
    rw [Finset.sum_congr rfl (fun q hq' => if_pos (hQ.mem_toFinset.1 hq')), Finset.sum_const,
      Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hQ]
  change (Submodule.Quotient.mk (hkS π I f u) : Jacquet π (unipB k (Fin n))) = _
  rw [e1, e3, hcard', ← GlobalTheory.T.sum_diag_pairs_toNat_eq_weighted_sum n x hx, zpow_natCast, ← Nat.cast_pow, jacBU_mk, Nat.cast_smul_eq_nsmul ℂ]
  rfl

end GlobalTheory.CompanionTheory.IwJac

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleSectionMemStandardOpenSubgroup
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem moduleSection_mem_standardOpenSubgroup {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (t : {r : ℝ // 0 < r}) :
    moduleSection w t ∈ standardOpenSubgroup F := by
  have h1 : ∀ s : {r : ℝ // 0 < r}, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((moduleSection w s : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro s v
    rw [← coe_finiteProj]
    simp [moduleSection, finiteProj_infiniteEmbedding]
  rw [mem_standardOpenSubgroup]
  intro v
  refine ⟨?_, ?_⟩
  · rw [h1]; exact one_mem _
  · rw [← map_inv, h1]; exact one_mem _

theorem differentiableOn_continuedLFunction :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker →
        DifferentiableOn ℂ χ.continuedLFunction {1}ᶜ := by
  intro F _ _ χ hU
  by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F,
      (χ.toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := h
    let w : InfinitePlace F := Classical.arbitrary _
    have hs : ∀ t : {x : ℝ // 0 < x}, χ.toIdele (moduleSection w t) = 1 := fun t ↦
      MonoidHom.mem_ker.1 (hU (moduleSection_mem_standardOpenSubgroup w t))
    have h0 : archExponent w χ = 0 := archExponent_unique w χ fun t ↦ by simp [hs t]
    have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
    have hd := HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ
    simpa [hτ0] using hd
  · exact (χ.differentiable_continuedLFunction h).differentiableOn

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormIntDilatedConst
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirStable

section Det

variable {k : Type} [Field k]

end Det

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def zM (m : ℕ) (u : kˣ) : Mir k m := levi k m (Matrix.GeneralLinearGroup.scalar (Fin m) u)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def normInt [MeasurableSpace k] (ν : Measure k) (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (L : Set (Fin n → k)) (v : V) (v' : V') : ℂ :=
  (((piHaar ν n).real L : ℝ) : ℂ)⁻¹ * ∫ x in L, coef T B v v' x ∂(piHaar ν n)

section Int

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isAddHaar_piHaar (m : ℕ) : (piHaar ν m).IsAddHaarMeasure := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  unfold piHaar
  infer_instance

end Int

section Int

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

end Int

end Rep

end GlobalTheory.CompanionTheory.MirStable

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorCommutesInfiniteGl
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

section General

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_sq_map_eq {B : LinearMap.BilinForm ℝ L} {b : Module.Basis ι ℝ L} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (φ ψ : L →ₗ⁅ℝ⁆ L)
    (hφ : ∀ X Y, B (φ X) (φ Y) = B X Y) (hψ : ∀ X, φ (ψ X) = X) :
    ∑ j, ε j • (UniversalEnvelopingAlgebra.ι ℝ (φ (b j)) * UniversalEnvelopingAlgebra.ι ℝ (φ (b j))) =
      ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)) := by
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  have h1 : ∀ j, u (φ (b j)) = ∑ i, (ε i * B (b i) (φ (b j))) • u (b i) := fun j => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (φ (b j))]
    simp only [map_sum, map_smul]
  have h2 : ∀ i, u (b i) = ∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j)) := fun i => by
    have e := congrArg φ (eq_sum_of_orthogonal hε horth (ψ (b i)))
    rw [hψ] at e
    conv_lhs => rw [e]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hφ (b j) (ψ (b i)), hψ]
  calc ∑ j, ε j • (u (φ (b j)) * u (φ (b j)))
      = ∑ j, ε j • (u (φ (b j)) * ∑ i, (ε i * B (b i) (φ (b j))) • u (b i)) :=
        Finset.sum_congr rfl fun j _ => by rw [← h1 j]
    _ = ∑ i, ∑ j, (ε i * (ε j * B (φ (b j)) (b i))) • (u (φ (b j)) * u (b i)) := by
        simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsymm (b i)]
        congr 1
        ring
    _ = ∑ i, ε i • ((∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))) * u (b i)) := by
        simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
    _ = ∑ i, ε i • (u (b i) * u (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h2 i]

end General

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem archTraceForm_AdLie (g : archGroup E a) (X Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a ((isExpLieAlgebra E a).AdLie g X) ((isExpLieAlgebra E a).AdLie g Y) =
      archTraceForm E a X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      mat (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1 := by
    rw [← mat_mul]
    simp
  change Matrix.trace ((mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (X : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) *
    (mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (Y : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a))) = _
  generalize mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) = A at *
  generalize mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = C at *
  generalize mat (X : ArchMatrix E a) = x
  generalize mat (Y : ArchMatrix E a) = y
  have e : A * x * C * (A * y * C) = A * (x * y * C) := by
    calc A * x * C * (A * y * C) = A * x * (C * A) * y * C := by simp only [Matrix.mul_assoc]
      _ = A * (x * y * C) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem AdLie_AdLie_inv (g : archGroup E a) (X : (isExpLieAlgebra E a).lieSubalgebra) :
    (isExpLieAlgebra E a).AdLie g ((isExpLieAlgebra E a).AdLie g⁻¹ X) = X := by
  have e := (isExpLieAlgebra E a).Ad_inv_Ad g⁻¹ ((isExpLieAlgebra E a).ofLie X)
  rw [inv_inv] at e
  exact Subtype.ext (congrArg Subtype.val e)

theorem AdU_casimir {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0) (g : archGroup E a) :
    (isExpLieAlgebra E a).AdU g (casimir b ε) = casimir b ε := by
  simp only [casimir, map_sum, map_smul, map_mul, IsExpLieAlgebra.AdU_ι]
  exact sum_sq_map_eq hε horth archTraceForm_symm _ ((isExpLieAlgebra E a).AdLie g⁻¹)
    (archTraceForm_AdLie g) (AdLie_AdLie_inv g)

theorem toGL_surjective : Function.Surjective (toGL E a) := fun y => by
  refine ⟨archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y), ?_⟩
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  ext i j
  simp

theorem omegaOp_comm_rt (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  obtain ⟨u, rfl⟩ := toGL_surjective y
  rw [← infEmb_eq]
  have hrt : ∀ φ : Sm E a, smL E a (rt E a (infEmb E a u) φ) = rtInf u (smL E a φ) := fun _ => rfl
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, hrt, uAction_rtInf,
    AdU_casimir b ε hε2 horth, hrt, smL_omegaOp]

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.LieCurve

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) : GL (Fin a) (Cinf E) where
  val := NormedSpace.exp (t • M)
  inv := NormedSpace.exp (-(t • M))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem expUnit_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    (expUnit E a M t).val = NormedSpace.exp (t • M) := rfl

theorem expUnit_inv_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    ((expUnit E a M t)⁻¹).val = NormedSpace.exp ((-t) • M) := by
  change NormedSpace.exp (-(t • M)) = _
  rw [neg_smul]

theorem hasDerivAt_exp (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • M)) (NormedSpace.exp (t • M) * M) t := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) M t

theorem continuous_exp_smul (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun t : ℝ => NormedSpace.exp (t • M) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp E a M t).continuousAt

theorem continuous_expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) : Continuous (expUnit E a M) := by
  refine Units.continuous_iff.2 ⟨continuous_exp_smul E a M, ?_⟩
  exact ((continuous_exp_smul E a M).comp continuous_neg).congr fun t => (expUnit_inv_val E a M t).symm

theorem expUnit_zero (M : Matrix (Fin a) (Fin a) (Cinf E)) : expUnit E a M 0 = 1 := by
  ext1
  rw [expUnit_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem expUnit_add (M : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expUnit E a M (s + t) = expUnit E a M s * expUnit E a M t := by
  ext1
  rw [Units.val_mul, expUnit_val, expUnit_val, expUnit_val, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right t)]

theorem expUnit_mem_unitary (M : Matrix (Fin a) (Fin a) (Cinf E)) (h : Mᴴ = -M) (t : ℝ) :
    (expUnit E a M t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have e : star (NormedSpace.exp (t • M)) = NormedSpace.exp (-(t • M)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h]
    simp
  rw [Matrix.mem_unitaryGroup_iff, expUnit_val, e]
  exact (expUnit E a M t).val_inv

def toLieL : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.of.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem toLieL_apply (M : Matrix (Fin a) (Fin a) (Cinf E)) : toLieL E a M = Matrix.of.symm M := rfl

theorem hasDerivAt_toL (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t : ℝ => toL (expUnit E a M t).val) (Matrix.of.symm M) 0 := by
  have h := (toLieL E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp E a M 0)
  have e : toLieL E a (NormedSpace.exp ((0 : ℝ) • M) * M) = Matrix.of.symm M := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  exact h.congr_deriv e

end

theorem exists_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      HasDerivAt (fun t => toL (c t).val) X 0 ∧
      ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) :=
  ⟨expUnit E a (Matrix.of X), continuous_expUnit E a _, expUnit_zero E a _, expUnit_add E a _,
    hasDerivAt_toL E a _, fun h t => expUnit_mem_unitary E a _ h t⟩

end GlobalTheory.CompanionTheory.LieCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHoldsStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiGP k := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.phiGP | exact GlobalTheory.CompanionTheory.LeibPhi.phiGP | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.phiGP <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZeroStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_product_left_rank_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (i : ℕ) (τ : MRep k (i + 1)) (σ : GRep k 0) (h : (i + 1) + 0 = (i + 0) + 1), IsSmooth τ.ρ → IsSmooth σ.ρ → MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | exact GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpenStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_on_subspace_open : ∀ (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε Z S} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNormStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_card_eq_abs_norm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (resCard (w.adicCompletion E) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm | exact GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm | (intros; apply GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm <;> assumption)
end

