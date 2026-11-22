import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeOperatorWeilRowUnipotentStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  first | exact @GlobalTheory.RootEx.RowSign.opE_om_rowE | exact GlobalTheory.RootEx.RowSign.opE_om_rowE | (intros; apply GlobalTheory.RootEx.RowSign.opE_om_rowE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecompositionStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  first | exact @GlobalTheory.RootEx.RadicalDecomp.succ_decomp | exact GlobalTheory.RootEx.RadicalDecomp.succ_decomp | (intros; apply GlobalTheory.RootEx.RadicalDecomp.succ_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatDistributionEqZeroBaireStatement
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  first | exact @GlobalTheory.BaireDistribution.eq_zero | exact GlobalTheory.BaireDistribution.eq_zero | (intros; apply GlobalTheory.BaireDistribution.eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatEventuallyInvariantOfContinuousAct
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by
  intro G X _ _ _ _ r h1 hmul hc Φ
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  obtain ⟨hlc, hcs⟩ := hΦ
  have hA : IsLocallyConstant (fun z : G × X => Φ.1 (r z.2 z.1)) :=
    hlc.comp_continuous (hc.comp continuous_swap)
  have hB : IsLocallyConstant (fun z : G × X => Φ.1 z.2) :=
    hlc.comp_continuous continuous_snd
  have key : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun u x => Φ.1 (r x u) = Φ.1 x) hcs ?_
    intro y _
    filter_upwards [hA.eventually_eq ((1 : G), y), hB.eventually_eq ((1 : G), y)] with z hz hz'
    rw [hz, hz']
    simp only [h1]
  have key' : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u⁻¹) = Φ.1 x := by
    have ht : Filter.Tendsto (fun u : G => u⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact ht.eventually key
  filter_upwards [key, key'] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ.1
  · exact hu x hx
  · by_cases hy : r x u ∈ tsupport Φ.1
    · have := hu' _ hy
      rw [← hmul, mul_inv_cancel, h1] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SplitWeil.FourierSurj

theorem hat_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have key := FourierPi.fourier_pi k n ψ hc h1 ν hν
  have hhat : ∀ f : (n → k) → ℂ,
      hat ψ ν f = fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro f
    funext y
    simp only [hat, dotProduct_comm y]
  have hmem : ∀ f ∈ SB (n → k), hat ψ ν f ∈ SB (n → k) := fun f hf => hhat f ▸ (key f hf).1
  refine ⟨fun Φ₀ => hmem _ Φ₀.2, fun g => ?_⟩
  have hcomp : ∀ (e : (n → k) ≃ₜ (n → k)), ∀ f ∈ SB (n → k), (fun x => f (e x)) ∈ SB (n → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hg' : (fun x => g.1 (-x)) ∈ SB (n → k) := hcomp (Homeomorph.neg _) _ g.2
  refine ⟨⟨_, hmem _ hg'⟩, ?_⟩
  funext u
  have hf : (fun x => g.1 (-(x + -u))) ∈ SB (n → k) := hcomp (Homeomorph.addRight (-u)) _ hg'
  have h2 := (key _ hf).2
  simp only [zero_add, neg_neg] at h2
  rw [← h2]
  show ∫ β, hat ψ ν (fun x => g.1 (-x)) β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν) = _
  congr 1
  funext y
  rw [hhat, ← integral_mul_const,
    ← integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) _ (-u)]
  congr 1
  funext x
  rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_dotProduct, neg_add_cancel_right]

end GlobalTheory.SplitWeil.FourierSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootExSource

theorem det_eq_one_of_unip {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (b : ι → ℕ)
    (M : Matrix ι ι k) (h : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hT : M.BlockTriangular b := fun r s hrs => by
    rw [h r s hrs.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hrs
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext r s
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, h _ _ (by rw [r.2, s.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_one]

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}

theorem mul_apply_of_inN {m : Type} {g : GL (n' ⊕ Fin c) k} (hg : InN p g)
    (x : Matrix m (n' ⊕ Fin c) k) (r : m) (s : n' ⊕ Fin c) :
    (x * g.val) r s = x r s + ∑ s', if lev p s' < lev p s then x r s' * g.val s' s else 0 := by
  have : x r s = (x * (1 : Matrix (n' ⊕ Fin c) (n' ⊕ Fin c) k)) r s := by rw [Matrix.mul_one]
  rw [this, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne, mul_zero, zero_add]
    rintro rfl
    exact lt_irrefl _ h
  · rw [hg s' s (not_lt.1 h), add_zero]

theorem affPt_nonfree (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, h]

theorem affPt_mul_nonfree {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : (affPt p x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [mul_apply_of_inN hg, affPt_nonfree _ _ _ _ h, Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ Free p (r, s') ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, lev, basePt] at h h' ⊢ <;> omega
    rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
  · rfl

theorem simpleSum_succ (g : GL (n' ⊕ Fin (c + 1)) k) :
    simpleSum g = ∑ l : Fin c, g.val (Sum.inr l.castSucc) (Sum.inr l.succ) := by
  unfold simpleSum
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Fin (c + 1) =>
    if j.val = (Fin.last c).val + 1 then g.val (Sum.inr (Fin.last c)) (Sum.inr j) else 0), add_zero]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.succ]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · simp
  · intro j _
    rw [if_neg]
    have := j.2
    simp only [Fin.val_last]
    omega

theorem ch_affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p x₀ e * g.val) = ch (affPt p x₀ e) + simpleSum g := by
  rw [simpleSum_succ, ch, ch, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_apply_of_inN hg, Finset.sum_eq_single (Sum.inr l.castSucc)]
  · rw [if_pos (by simp [lev]), affPt_nonfree _ _ _ (Sum.inr l.castSucc) (by simp [Free])]
    simp [basePt]
  · intro s' _ hs
    split_ifs with h'
    · have : ¬ Free p ((Sum.inr l : n ⊕ Fin c), s') ∧ basePt c x₀ (Sum.inr l) s' = 0 := by
        rcases s' with s' | s' <;> simp [Free, lev, basePt, Fin.ext_iff] at hs h' ⊢ <;> omega
      rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
    · rfl
  · simp

def linPart (n : Type) [DecidableEq n] (p : ℕ) (g : GL (n' ⊕ Fin (c + 1)) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g.val b.1.2 a.1.2 else 0

open Classical in
theorem det_linPart {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) : (linPart n p g).det = 1 := by
  rw [← det_transpose]
  refine det_eq_one_of_unip (fun a => lev p a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linPart, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]

open Classical in
theorem affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e * g.val = affPt p x₀ ((linPart n p g).mulVec e +
      fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases h : Free p (r, s)
  · have key : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
        ∑ s', (if h : Free p (r, s') then e ⟨(r, s'), h⟩ else 0) * g.val s' s := by
      have h1 : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
          ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), (if b.1 = r then g.val b.2 s else 0) *
            (if h : Free p b then e ⟨b, h⟩ else 0) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free p b)]
        rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ Free p b} => _)
          (fun b _ => by rw [dif_neg b.2, mul_zero]), add_zero]
        simp only [Matrix.mulVec, dotProduct, linPart, of_apply]
        refine Finset.sum_congr rfl fun b _ => by rw [dif_pos b.2]
      rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single r]
      · simp [mul_comm]
      · intro r' _ hr
        simp [hr]
      · simp
    unfold affPt
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, of_apply, dif_pos h, Pi.add_apply, key]
    simp only [Matrix.mul_apply, Matrix.sub_apply, of_apply]
    ring
  · rw [affPt_mul_nonfree hg _ _ _ _ h, affPt_nonfree _ _ _ _ h]

private theorem secondCountable_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact secondCountable_of_proper

theorem opE_om_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n' (c + 1) p, opE ψ ν p (om μ g 1 Φ) = (ψ (simpleSum g) : ℂ) • opE ψ ν p Φ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hgN
  classical
  have := secondCountable_local k
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n' (c + 1) p
  have hg : InN p g := (h1 g).1 hgN
  have hdet := h3 g hgN
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : om μ g 1 Φ = fun x => Φ (x * g.val) := by
    funext x
    simp [om, hdet, hn1]
  funext x₀
  rw [hom, Pi.smul_apply, smul_eq_mul]
  unfold opE
  set v : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2 with hv
  set F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) with hF
  let G : GL {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart n p g) (by rw [det_linPart hg]; exact one_ne_zero)
  have hGval : G.val = linPart n p g := rfl
  have hGdet : Matrix.GeneralLinearGroup.det G = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hGval, det_linPart hg]; rfl
  have hcov := (GlobalTheory.SplitWeil.linear_change_of_variables k {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} n ν).1 G
    (fun e => F (e + v))
  rw [hGdet, hn1, inv_one, one_smul, hGval] at hcov
  have hint : ∀ e, Φ (affPt p x₀ e * g.val) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (simpleSum g) : ℂ) * F ((linPart n p g).mulVec e + v) := by
    intro e
    simp only [hF]
    rw [hv, ← affPt_mul hg, ch_affPt_mul hg, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  simp only [hint]
  rw [integral_const_mul, hcov]
  congr 1
  exact integral_add_right_eq_self F v

end GlobalTheory.RootExSource
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpanStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  first | exact @GlobalTheory.TensHead.simpleOver_tensKer | exact GlobalTheory.TensHead.simpleOver_tensKer | (intros; apply GlobalTheory.TensHead.simpleOver_tensKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCorner
section
namespace GlobalTheory.SplitFlip

def vertexDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vertexDiff_tgt (e : Edge) : vertexDiff e.tgt = vertexDiff e.src + 1 := by
  cases e <;> simp [vertexDiff, Edge.src, Edge.tgt] <;> omega

theorem IsPath.pairwise_vertexDiff : ∀ {γ : List Edge}, IsPath γ →
    γ.Pairwise fun a b => vertexDiff a.src < vertexDiff b.src
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    unfold IsPath at h
    rw [List.isChain_cons_cons] at h
    have ih := IsPath.pairwise_vertexDiff (γ := b :: t) h.2
    have hab : vertexDiff a.src < vertexDiff b.src := by
      rw [← h.1, vertexDiff_tgt]; omega
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hc)

theorem IsPath.eq_of_vertexDiff_eq {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : vertexDiff a.src = vertexDiff b.src) : a = b := by
  by_contra hne
  have hpw := hγ.pairwise_vertexDiff
  have key : ∀ {l : List Edge}, l.Pairwise (fun a b => vertexDiff a.src < vertexDiff b.src) →
      ∀ {a b : Edge}, a ∈ l → b ∈ l → a ≠ b → vertexDiff a.src ≠ vertexDiff b.src := by
    intro l hl
    induction hl with
    | nil => intro a b ha; simp at ha
    | @cons x l hx _ ih =>
      intro a b ha hb hab
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact (hx b hb').ne
      · exact (hx a ha').ne'
      · exact ih ha' hb' hab
  exact key hpw ha hb hne h

theorem pathAvoid : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  intro γ i j hγ hp b hb
  have hθ : Edge.theta i j ∈ γ := hp.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hp.subset (by simp)
  refine ⟨fun hs => ?_, fun ht => ?_⟩
  · have := hγ.eq_of_vertexDiff_eq hb hx (by rw [hs]; simp [vertexDiff, Edge.src])
    subst this
    simp [Edge.src] at hs
  · have h1 := vertexDiff_tgt b
    rw [ht] at h1
    have := hγ.eq_of_vertexDiff_eq hb hθ (by simp [vertexDiff, Edge.src] at h1 ⊢; omega)
    subst this
    simp [Edge.tgt] at ht

end GlobalTheory.SplitFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabiliserFiniteCosetsMod
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem stabiliser_finite_cosets_mod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (M : Submodule 𝒪[k] (ι → k)) (S : Finset (ι → k)) (hM : M.FG) (hS : IsReps ϖ M S) :
    ∃ T : Finset (GL ι k), (∀ t ∈ T, act t M = M) ∧ ∀ t : GL ι k, act t M = M →
      ∃ t₀ ∈ T, ∃ j : GL ι k, act j M = M ∧ MapsInto (j.val - 1) M (ϖ • M) ∧ t = t₀ * j := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hmem : ∀ t : GL ι k, act t M = M → ∀ x ∈ M, t.val *ᵥ x ∈ M := fun t ht x hx => by
    have h : t.val *ᵥ x ∈ act t M := mem_act.2 ⟨x, hx, rfl⟩
    rwa [ht] at h
  have hsM : ∀ x : s, x.1 ∈ M := fun x => hs ▸ Submodule.subset_span x.2
  have hex : ∀ (t : {t : GL ι k // act t M = M}) (x : s), ∃ r : S, t.1.val *ᵥ x.1 - r.1 ∈ ϖ • M := by
    intro t x
    obtain ⟨r, hr, -⟩ := hS.2 _ (hmem t.1 t.2 x.1 (hsM x))
    exact ⟨⟨r, hr.1⟩, hr.2⟩
  choose f hf using hex
  have hsec : ∀ y : Set.range f, ∃ t, f t = y.1 := fun y => y.2
  choose g hg using hsec
  have : Fintype (Set.range f) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y => (g y).1, ?_, fun t ht => ?_⟩
  · intro t ht
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    exact (g y).2
  · set t₀ := g ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩ with ht₀
    have hft : f t₀ = f ⟨t, ht⟩ := hg _
    have hinv : act (t₀.1)⁻¹ M = M := by
      have h := act_mul (t₀.1)⁻¹ t₀.1 M
      rw [inv_mul_cancel, act_one, t₀.2] at h
      exact h.symm
    refine ⟨t₀.1, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (t₀.1)⁻¹ * t, ?_, ?_, ?_⟩
    · rw [act_mul, ht, hinv]
    · intro v hv
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        have h1 := hf ⟨t, ht⟩ ⟨x, hx⟩
        have h2 := hf t₀ ⟨x, hx⟩
        rw [hft] at h2
        have h3 := sub_mem h1 h2
        rw [sub_sub_sub_cancel_right] at h3
        obtain ⟨w, hw, hw'⟩ := mem_smul_iff.1 h3
        refine mem_smul_iff.2 ⟨_, hmem _ hinv w hw, ?_⟩
        rw [← Matrix.mulVec_smul, hw', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Units.inv_mul, Units.val_mul]
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ a hx
    · rw [mul_inv_cancel_left]

end GlobalTheory.RootEx.UnfoldShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorMaximalStableContainsLeftKernelStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_maximalStable_contains_leftKernel : ∀ {M₀ V : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup V] [Module ℂ V]
    (Op₀ : Set (Module.End ℂ M₀)) (B : Set (Module.End ℂ V)) (Rel₀ K₀ : Submodule ℂ M₀),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → N ≠ ⊤ → N ≤ K₀) →
    K₀ ≠ ⊤ → GlobalTheory.TensHead.Stab Op₀ K₀ →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] V),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N') → GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) U → N' ≤ U → U = N' ∨ U = ⊤) →
      ∀ x ∈ K₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N' := by
  first | exact @GlobalTheory.TensHead.tens_maxStab_contains_left_ker | exact GlobalTheory.TensHead.tens_maxStab_contains_left_ker | (intros; apply GlobalTheory.TensHead.tens_maxStab_contains_left_ker <;> assumption)
end

