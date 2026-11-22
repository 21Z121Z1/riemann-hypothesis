import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling

namespace GlobalTheory.ZonalCellDecomposition

def blkEquiv (l t : ℕ) : Fin (l * t) ≃ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin l) (Fin t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mtor {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GL (A ⊕ D) k :=
  torusElt k (A ⊕ D) ϖ (Sum.elim 0 e)

def dcell {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    Set (GL (A ⊕ D) k) :=
  DoubleCoset.doubleCoset (mtor ϖ e) (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D : Set (GL (A ⊕ D) k))
    (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D)

def IsBiType {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ)
    (φ : GL (A ⊕ D) k → ℂ) : Prop :=
  ∀ j ∈ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    ∀ g, φ (j * g) = (ξ d : ℂ) * φ g ∧ φ (g * j) = (ξ d : ℂ) * φ g

def sumAbs {D : Type} [Fintype D] (e : D → ℤ) : ℤ := ∑ i, |e i|

def zonalInt {N : ℕ} [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) : ℂ :=
  ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * g) ∂μK

def borelParam {N : ℕ} (q : ℕ) (α : Fin N → ℂˣ) (x : Fin N) : ℂ :=
  (α x : ℂ) * (q : ℂ) ^ (((x : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)

end GlobalTheory.ZonalCellDecomposition
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfOrthogonalSchrodingerGaussianStatement
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by
  first | exact @GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | exact GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | (intros; apply GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology

namespace GlobalTheory.SBUniform

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_deep (a : ℤ) : IsOpen {x : k | Deep a x} := by
  have hγ : (uniformizer k ^ a : ValueGroupWithZero k) ≠ 0 := zpow_ne_zero _ uniformizer_ne_zero
  unfold Deep
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hγ, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hx ⊢

  have h := (valuation k).map_add (z - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hz.le hx)

theorem eventually_deep_subset {s : Set k} (hs : s ∈ 𝓝 (0 : k)) :
    ∀ᶠ M : ℕ in atTop, ∀ x : k, Deep (M : ℤ) x → x ∈ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs

  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) γ
  filter_upwards [eventually_ge_atTop M₀] with M hM x hx
  apply hγ
  unfold Deep at hx
  show valuation k x < γ
  have hle : uniformizer k ^ (M : ℤ) ≤ uniformizer k ^ (M₀ : ℤ) :=
    zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le (by exact_mod_cast hM)
  have hM₀' : uniformizer k ^ (M₀ : ℤ) < γ := by rwa [zpow_natCast]
  exact hx.trans_lt (hle.trans_lt hM₀')

theorem exists_deep_subset {n : Type} [Fintype n] {s : Set (Matrix n n k)} (hs : s ∈ 𝓝 (0 : Matrix n n k)) :
    ∃ M : ℕ, ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → y ∈ s := by
  have hs' : s ∈ 𝓝 (0 : n → n → k) := hs
  rw [nhds_pi] at hs'
  obtain ⟨I, -, t, ht, hts⟩ := Filter.mem_pi.1 hs'

  have ht' : ∀ i, ∃ J : Set n, J.Finite ∧ ∃ u : n → Set k, (∀ j, u j ∈ 𝓝 (0 : k)) ∧ J.pi u ⊆ t i := by
    intro i
    have hi : t i ∈ 𝓝 (0 : n → k) := ht i
    rw [nhds_pi] at hi
    exact Filter.mem_pi.1 hi
  choose J _ u hu hJu using ht'
  have hev : ∀ᶠ M : ℕ in atTop, ∀ i j, ∀ x : k, Deep (M : ℤ) x → x ∈ u i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_deep_subset (hu i j)
  obtain ⟨M, hM⟩ := hev.exists
  exact ⟨M, fun y hy => hts (Set.mem_pi.2 fun i _ => hJu i (Set.mem_pi.2 fun j _ => hM i j _ (hy i j)))⟩

private theorem deep_neg {a : ℤ} {x : k} (h : Deep a x) : Deep a (-x) := by
  unfold Deep at h ⊢
  rwa [Valuation.map_neg]

private theorem deep_add {a : ℤ} {x y : k} (hx : Deep a x) (hy : Deep a y) : Deep a (x + y) := by
  unfold Deep at hx hy ⊢
  exact ((valuation k).map_add x y).trans (max_le hx hy)

private theorem deep_zero' (a : ℤ) : Deep a (0 : k) := by
  unfold Deep
  simp

private theorem deep_of_le' {a b : ℤ} (hab : a ≤ b) {x : k} (h : Deep b x) : Deep a x := by
  unfold Deep at h ⊢
  exact h.trans (zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab)

private theorem exists_deep_neg_natCast (x : k) : ∃ N : ℕ, Deep (-(N : ℤ)) x := by
  unfold Deep
  by_cases hx : valuation k x = 0
  · exact ⟨0, by simp [hx]⟩

  obtain ⟨N, hN⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨N, ?_⟩
  rw [Units.val_mk0] at hN
  have hpos : (0 : ValueGroupWithZero k) < uniformizer k ^ N := pow_pos uniformizer_pos N
  have hx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_iff.2 hx
  rw [_root_.zpow_neg, zpow_natCast]
  exact ((lt_inv_comm₀ hpos hx0).1 hN).le

private theorem isOpen_setOf_forall_deep {n : Type} [Fintype n] (a : ℤ) :
    IsOpen {y : Matrix n n k | ∀ i j, Deep a (y i j)} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_deep (k := k) a).preimage (continuous_id.matrix_elem i j)

theorem exists_bound_period : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n], ∀ Φ ∈ SB (Matrix n n k),
    ∃ N M : ℕ, (∀ x, Φ x ≠ 0 → ∀ i j, Deep (-(N : ℤ)) (x i j)) ∧
      ∀ x y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x := by
  intro k _ _ _ _ n _ _ Φ hΦ
  have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨hlc, hcs⟩ := hΦ'
  have hC : IsCompact (tsupport Φ) := hcs
  have hzero : ∀ z, z ∉ tsupport Φ → Φ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport Φ h)

  let U : ℕ → Set (Matrix n n k) := fun N => {x | ∀ i j, Deep (-(N : ℤ)) (x i j)}
  have hUm : Monotone U := fun N N' h x hx i j =>
    deep_of_le' (neg_le_neg (by exact_mod_cast h)) (hx i j)
  have hUcov : tsupport Φ ⊆ ⋃ N, U N := by
    intro x _
    have hev : ∀ᶠ N : ℕ in atTop, ∀ i j, Deep (-(N : ℤ)) (x i j) := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      obtain ⟨N₀, hN₀⟩ := exists_deep_neg_natCast (x i j)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact deep_of_le' (neg_le_neg (by exact_mod_cast hN)) hN₀
    obtain ⟨N, hN⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨N, hN⟩ := hC.elim_directed_cover U (fun N => isOpen_setOf_forall_deep _) hUcov hUm.directed_le

  let W : ℕ → Set (Matrix n n k) :=
    fun M => {x | ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x}
  have hWm : Monotone W := fun M M' h x hx y hy =>
    hx y fun i j => deep_of_le' (by exact_mod_cast h) (hy i j)
  have hWo : ∀ M, IsOpen (W M) := by
    intro M
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hD : {y : Matrix n n k | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 (0 : Matrix n n k) :=
      (isOpen_setOf_forall_deep _).mem_nhds fun i j => deep_zero' _
    have hD' : (fun z : Matrix n n k => z - x) ⁻¹' {y | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 x := by
      apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      simpa using hD
    refine Filter.mem_of_superset hD' fun z hz y hy => ?_
    have hz' : ∀ i j, Deep (M : ℤ) ((z - x) i j) := hz
    have h1 : Φ (x + ((z - x) + y)) = Φ x :=
      hx _ fun i j => by simpa using deep_add (hz' i j) (hy i j)
    have h2 : Φ (x + (z - x)) = Φ x := hx _ hz'
    rw [add_sub_cancel] at h2
    have he : x + ((z - x) + y) = z + y := by abel
    rw [he] at h1
    rw [h1, h2]
  have hWcov : tsupport Φ ⊆ ⋃ M, W M := by
    intro x _
    have hs : {y : Matrix n n k | Φ (x + y) = Φ x} ∈ 𝓝 (0 : Matrix n n k) := by
      apply IsOpen.mem_nhds
      · exact (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
      · simp
    obtain ⟨M, hM⟩ := exists_deep_subset hs
    exact Set.mem_iUnion.2 ⟨M, fun y hy => hM y hy⟩
  obtain ⟨M, hM⟩ := hC.elim_directed_cover W hWo hWcov hWm.directed_le
  refine ⟨N, M, fun x hx i j => hN (subset_tsupport Φ hx) i j, fun x y hy => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · exact hM hx y hy
  by_cases hxy : x + y ∈ tsupport Φ
  · have h := hM hxy (-y) fun i j => by simpa using deep_neg (hy i j)
    rw [add_neg_cancel_right] at h
    exact h.symm
  · rw [hzero _ hx, hzero _ hxy]

end GlobalTheory.SBUniform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

theorem rowE_zero_eq_one {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    rowE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hC : (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) = 0 := by
    ext l s
    simp
  show Matrix.fromBlocks 1 0
      (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) 1 = 1
  rw [hC, Matrix.fromBlocks_one]

theorem colE_zero_eq_one {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    colE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hB : (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) = 0 := by
    ext r i
    simp
  show Matrix.fromBlocks 1
      (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) 0 1 = 1
  rw [hB, Matrix.fromBlocks_one]

private theorem sigmaCompactSpace_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
  have hδ : (1 : ValueGroupWithZero k) < γ⁻¹ := one_lt_inv_iff₀.mpr ⟨hγ0, hγ1⟩
  refine ⟨⟨fun m : ℕ => {x : k | valuation k x ≤ γ⁻¹ ^ m},
    fun m => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact MulArchimedean.arch (valuation k x) hδ

private theorem fourier_fourier_eq_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    [DecidableEq n] (ψ : AddChar k Circle) (ν : Measure k) [SigmaFinite ν] [ν.IsAddHaarMeasure]
    (hF : ∀ f ∈ SB (n → k), ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0)
    (f : (n → k) → ℂ) (hf : f ∈ SB (n → k)) (z : n → k) :
    ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ z) : ℂ)
      ∂(Measure.pi fun _ => ν) = f (-z) := by
  have hτ : (fun x : n → k => f (x - z)) ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_sub_right z), hf.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have key : ∀ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
      * (ψ (y ⬝ᵥ z) : ℂ) = ∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro y
    rw [← integral_mul_const,
      ← integral_add_right_eq_self (fun x : n → k => f (x - z) * (ψ (x ⬝ᵥ y) : ℂ)) z]
    congr 1
    funext x
    simp only [add_sub_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul,
      dotProduct_comm z y]
    ring
  calc _ = ∫ y : n → k, (∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) := by
          congr 1
          funext y
          exact key y
    _ = f (0 - z) := hF _ hτ
    _ = f (-z) := by rw [zero_sub]

theorem exDown_exUp_and_exUp_exDown : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → exDown ν p σ (exUp ν p σ l) v = l v) ∧ (IsNEquiv ψ (p + 1) σ l → exUp ν p σ (exDown ν p σ l) v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψc hψ1 ν hsd A _ _ σ hσ l v
  have : ν.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.rootExchange_support_and_fourier_relation k n c p hp hpc ψ hψc hψ1 ν A σ hσ l v
  have hF := GlobalTheory.T.fourier_transform_inversion_localFieldPi k n ψ hψc hψ1 ν hsd
  constructor
  · intro hN
    obtain ⟨hSB, -, hint⟩ := hT.1 hN
    have h1 : exDown ν p σ (exUp ν p σ l) v
        = ∫ β : n → k, ∫ u : n → k, (fun u : n → k => l (σ (rowE c p u) v)) u * (ψ (u ⬝ᵥ β) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exDown
      congr 1
      funext β
      rw [hint β]
      congr 1
      funext u
      ring
    rw [h1, (hF _ hSB).2]
    simp [rowE_zero_eq_one]
  · intro hN
    obtain ⟨hSB, hcomm⟩ := hT.2 hN
    have : SigmaCompactSpace k := sigmaCompactSpace_nonarchimedeanLocalField k
    have : SigmaFinite ν := inferInstance
    have hF2 := fun f hf => (hF f hf).2
    have hG := (hF _ hSB).1
    have hGG := (hF _ hG).1
    have h1 : exUp ν p σ (exDown ν p σ l) v
        = ∫ u : n → k, ∫ y : n → k, (∫ x : n → k, (∫ β : n → k, l (σ (colE c (p + 1) β) v)
            * (ψ (β ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (x ⬝ᵥ y) : ℂ)
            ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ u) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exUp exDown
      congr 1
      funext u
      rw [fourier_fourier_eq_neg ψ ν hF2 _ hG u]
      congr 1
      funext β
      rw [hcomm u β, dotProduct_neg, dotProduct_comm]
      ring
    rw [h1, hF2 _ hGG]
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    rw [hF2 _ hSB]
    show l (σ (colE c (p + 1) 0) v) = l v
    rw [colE_zero_eq_one, map_one]
    rfl

end GlobalTheory.RootEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAverage
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.WordGrowth

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {J : Subgroup G}

theorem _root_.GlobalTheory.WordGrowth.exists_average
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {J : Subgroup G}
    (hπ : _root_.GlobalTheory.PRep.IsSmooth π) (hJ : IsCompact (↑J : Set G)) (u : V) :
          ∃ t ∈ _root_.GlobalTheory.PRep.fixed π J,
            ∀ (f : V →ₗ[ℂ] ℂ),
              (∀ j ∈ J, (f : V → ℂ) (((π : G → V →ₗ[ℂ] V) j : V → V) u) = (f : V → ℂ) u) →
                (f : V → ℂ) t = (f : V → ℂ) u := by

  have hK : IsOpen {g : G | π g u = u} := hπ u
  obtain ⟨F, hF⟩ := hJ.elim_finite_subcover
    (fun j : J => (fun g : G => (j : G)⁻¹ * g) ⁻¹' {g : G | π g u = u})
    (fun j => hK.preimage (continuous_const.mul continuous_id))
    (by
      intro g hg
      exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    apply (F.finite_toSet.image (fun j : J => π (j : G) u)).subset
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, hjF, hj⟩ := Set.mem_iUnion₂.1 (hF hg)
    refine ⟨j, hjF, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hj
    show π j u = π g u
    calc π (j : G) u = π j (π ((j : G)⁻¹ * g) u) := by rw [hj]
      _ = π g u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  set O := hfin.toFinset with hO
  have hmem : ∀ v, v ∈ O ↔ ∃ g ∈ J, π g u = v := by
    intro v
    simp [O]
  have huO : u ∈ O := (hmem u).2 ⟨1, J.one_mem, by simp⟩
  have hcard : (O.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨u, huO⟩).ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · simp only [_root_.GlobalTheory.PRep.fixed, _root_.GlobalTheory.PRep.eig]
    simp
    intro a ha
    congr 1
    apply Finset.sum_nbij' (fun v => π a v) (fun v => π a⁻¹ v)
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a * g, J.mul_mem ha hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a⁻¹ * g, J.mul_mem (J.inv_mem ha) hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  · intro f hf
    rw [map_smul, map_sum, smul_eq_mul]
    rw [Finset.sum_congr rfl (g := fun _ => f u) ?_]
    · rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact hf g hg

end GlobalTheory.WordGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactSubgroup
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.UnipCompact

variable {n : Type}

theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

theorem isClosed_unipOf (c : n → ℤ) : IsClosed (unipOf k c : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (unipOf k c : Set (GL n k)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by
  have key : ∀ u ∈ unipOf k c, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    by_cases h : c i < c j
    · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      nlinarith [Int.natCast_nonneg m]
    · rw [mem_unipOf.1 hu i j h]
      refine Filter.Eventually.of_forall fun m => ?_
      by_cases hij : i = j
      · subst hij
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

theorem exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (isClosed_unipOf c)

end GlobalTheory.UnipCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegral
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.MellinPoly

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < (resCard k : ℝ) := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hq0 : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hz : (resCard k : ℝ) ^ (-SmGL.ord k x) ≠ 0 := (zpow_pos hq _).ne'
  unfold absPow
  simp only [MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hz),
    Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_int_mul, ← Complex.ofReal_log (zpow_pos hq _).le,
    Real.log_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_log hq.le]
  push_cast
  congr 1
  try simp only [Complex.ofReal_intCast, Complex.ofReal_natCast]
  ring

end GlobalTheory.MellinPoly
end
end

