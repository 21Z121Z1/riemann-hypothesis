import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallyEqOfAdditiveOfHasFDerivAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LieCharpolyRootPairs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtCoordinateZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelExp

variable {X : Scheme.{0}} {G : Over X}

abbrev pt {x : Sp ℂ ⟶ X} (a : Over.mk x ⟶ G) : Sp ℂ ⟶ G.left := a.left

abbrev crd {Z : Scheme.{0}} (U : Z.Opens) {κ : Type} (t : κ → Γ(Z, U)) (z : Sp ℂ ⟶ Z) : κ → ℂ :=
  fun i => valAt' z U (t i)

variable [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} {U : G.left.Opens}
  {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}

abbrev crd0 (t : Fin g → Γ(G.left, U)) {x : Sp ℂ ⟶ X} (a : Over.mk x ⟶ G) : Fin g → ℂ :=
  crd U t (pt a) - crd U t (pt (1 : Over.mk x ⟶ G))

theorem exists_centred_chart (hy : HolAt y b₀) {N : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} (hN : IsOpen N)
    (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U) (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O)
    (hσ : IsHolTo N σ) (hσN : ∀ q ∈ N, σ q ≫ G.hom = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i)
    (hinv : ∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ G.left), x ≫ G.hom = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, crd U f x) ∈ O →
      (b, crd U t x) ∈ N ∧ σ (b, crd U t x) = x) :
    ∃ s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G),
      HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a := by
  classical
  let c : (Fin m → ℂ) → (Fin g → ℂ) := fun b => crd U t (pt (1 : Over.mk (y b) ⟶ G))
  have hc : AnalyticAt ℂ c b₀ := (HolAt.one (G := G) hy).analyticAt_pi hU t
  let τ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) := fun q => (q.1, q.2 + c q.1)
  have hτ : AnalyticAt ℂ τ (b₀, 0) :=
    analyticAt_fst.prod (analyticAt_snd.add (AnalyticAt.comp (g := c) hc analyticAt_fst))
  have hτ0 : τ (b₀, 0) ∈ N := by
    have := (hinv b₀ _ (Over.w (1 : Over.mk (y b₀) ⟶ G)) hU hO).1
    simpa only [τ, zero_add] using this
  let s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G) := fun b w =>
    if h : τ (b, w) ∈ N then Over.homMk (σ (τ (b, w))) (hσN _ h).1 else 1
  have hs : ∀ q, τ q ∈ N → pt (s q.1 q.2) = σ (τ q) := fun q hq => by
    have : s q.1 q.2 = Over.homMk (σ (τ q)) (hσN _ hq).1 := dif_pos hq
    rw [this]; rfl
  have hev : ∀ᶠ q in 𝓝 (b₀, (0 : Fin g → ℂ)), τ q ∈ N := hτ.continuousAt.eventually (hN.mem_nhds hτ0)
  refine ⟨s, (HolAt.comp ⟨N, hN, hτ0, hσ⟩ hτ).congr (hev.mono fun q hq => (hs q hq).symm), hev.mono fun q hq => ?_,
    fun b a ha hf => ?_⟩
  · have : crd U t (pt (s q.1 q.2)) = q.2 + c q.1 := by
      rw [hs q hq]; exact funext (hσN _ hq).2.2
    exact sub_eq_iff_eq_add.2 this
  · obtain ⟨h1, h2⟩ := hinv b _ (Over.w a) ha hf
    have e : τ (b, crd0 t a) = (b, crd U t (pt a)) := Prod.ext rfl (sub_add_cancel _ _)
    refine Over.OverMorphism.ext ((hs (b, crd0 t a) (e ▸ h1)).trans ?_)
    rw [e]; exact h2

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {β : E → (Fin m → ℂ)}
  {a : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : E}

omit [FiniteDimensional ℂ E] in
theorem HolAt.one_of (ha : HolAt (fun w => pt (a w)) w₀) :
    HolAt (fun w => pt (1 : Over.mk (y (β w)) ⟶ G)) w₀ := by
  simpa only [pow_zero] using ha.pow 0

theorem HolAt.analyticAt_coordinate_zero (ha : HolAt (fun w => pt (a w)) w₀) (h1 : a w₀ = 1)
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) : AnalyticAt ℂ (fun w => crd0 t (a w)) w₀ :=
  (ha.analyticAt_pi (by rw [h1]; exact hU) t).sub (ha.one_of.analyticAt_pi hU t)

theorem HolAt.eventually_near (ha : HolAt (fun w => pt (a w)) w₀) (hβ : ContinuousAt β w₀) (h1 : a w₀ = 1)
    (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U)
    (hO : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O) :
    ∀ᶠ w in 𝓝 w₀, ⊤ ≤ pt (a w) ⁻¹ᵁ U ∧ (β w, crd U f (pt (a w))) ∈ O := by
  have hU' : ⊤ ≤ pt (a w₀) ⁻¹ᵁ U := by rw [h1]; exact hU
  refine (ha.eventually_mem hU').and ((hβ.prodMk (ha.analyticAt_pi hU' f).continuousAt).eventually
    (hOo.mem_nhds ?_))
  simpa only [h1] using hO

end Family

theorem exists_local_exp [IsCommMonObj G]
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
        s q.1 (E (q.1, q.2.1 + q.2.2)) = s q.1 (E (q.1, q.2.1)) * s q.1 (E (q.1, q.2.2)) := by
  have hs0 : ∀ᶠ b in 𝓝 b₀, s b 0 = 1 := by
    filter_upwards [HolAt.eventually_near (β := fun b => b) (a := fun _ => 1) (HolAt.one hy) continuousAt_id rfl
      hOo hU hO] with b hb
    simpa only [crd0, sub_self] using hs3 b 1 hb.1 hb.2
  have hprod : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2.1 * s q.1 q.2.2))
      (b₀, 0, 0) := by
    have k1 := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.1)) (v₀ := (b₀, 0, 0))
      hs1 (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
    have k2 := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.2)) (v₀ := (b₀, 0, 0))
      hs1 (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd))
    exact HolAt.mul (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => y q.1)
      (a := fun q => s q.1 q.2.1) (b := fun q => s q.1 q.2.2) k1 k2
  have h11 : s b₀ 0 * s b₀ 0 = 1 := by rw [hs0.self_of_nhds, _root_.mul_one]
  let M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun q => crd0 t (s q.1 q.2.1 * s q.1 q.2.2)
  have hMa : AnalyticAt ℂ M (b₀, 0, 0) :=
    HolAt.analyticAt_coordinate_zero (β := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => q.1)
      (a := fun q => s q.1 q.2.1 * s q.1 q.2.2) hprod h11 hU
  have hM : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
      s q.1 (M q) = s q.1 q.2.1 * s q.1 q.2.2 :=
    (HolAt.eventually_near (β := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => q.1)
      (a := fun q => s q.1 q.2.1 * s q.1 q.2.2) hprod
      continuousAt_fst h11 hOo hU hO).mono fun q hq => hs3 _ _ hq.1 hq.2
  obtain ⟨E, L, hE, hL, h0, hLE, hadd⟩ := hexp m g b₀ M hMa (by
      filter_upwards [hs2, (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually hs0] with q h1 h2
      show crd0 t (s q.1 q.2 * s q.1 0) = q.2
      rw [h2, _root_.mul_one, h1])
    (Eventually.of_forall fun q => by simp only [M, mul_comm]) (by
      have t1 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        (q.1, q.2.1, q.2.2.1)) (by fun_prop) (b₀, 0, 0, 0)
      have t2 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        (q.1, q.2.2.1, q.2.2.2)) (by fun_prop) (b₀, 0, 0, 0)
      filter_upwards [t1.eventually hM, t2.eventually hM] with q h1 h2
      show crd0 t (s q.1 (M _) * s q.1 q.2.2.2) = crd0 t (s q.1 q.2.1 * s q.1 (M _))
      rw [h1, h2, _root_.mul_assoc])
  refine ⟨E, L, hE, hL, h0, hLE, ?_⟩
  have hEt : Tendsto E (𝓝 (b₀, 0)) (𝓝 0) := by
    have := hE.continuousAt.tendsto
    rwa [h0.self_of_nhds.1] at this
  have t1 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.1))
    (by fun_prop) (b₀, 0, 0)
  have t2 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.2))
    (by fun_prop) (b₀, 0, 0)
  have t3 := ((continuous_fst.tendsto (b₀, (0 : Fin g → ℂ), (0 : Fin g → ℂ))).prodMk_nhds
    ((hEt.comp t1).prodMk_nhds (hEt.comp t2)))
  filter_upwards [hadd, t3.eventually hM] with q h1 h2
  rw [h1]
  exact h2

theorem exists_global_exp [IsCommMonObj G]
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    {B : Set (Fin m → ℂ)} (hB : B ∈ 𝓝 b₀)
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ)
      (Q : Set ((Fin m → ℂ) × (Fin g → ℂ))) (L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ 0 < r ∧ IsOpen Q ∧ (∀ b z w, e b (z + w) = e b z * e b w) ∧
      (∀ b ∈ B', (∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (b, z)) ∧
        ⊤ ≤ pt (1 : Over.mk (y b) ⟶ G) ⁻¹ᵁ U ∧ (b, crd U f (pt (1 : Over.mk (y b) ⟶ G))) ∈ O ∧ (b, 0) ∈ Q ∧
        HasFDerivAt (fun z => crd U t (pt (e b z))) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
        L (b, 0) = 0 ∧ AnalyticAt ℂ L (b, 0) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
        e b (L (b, crd0 t a)) = a := by
  obtain ⟨E, L, hE, hL, h0, hLE, hadd⟩ := exists_local_exp hexp hy hOo hU hO hs1 hs2 hs3
  have hE0 : E (b₀, 0) = 0 := h0.self_of_nhds.1
  have hL0 : L (b₀, 0) = 0 := by
    have := hLE.self_of_nhds.1
    rwa [hE0] at this
  have hτ : AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, E q)) (b₀, 0) := analyticAt_fst.prod hE
  have hψ : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 (E q))) (b₀, 0) := by
    have := HolAt.comp (a := fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2))
      (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, E q)) (v₀ := (b₀, 0)) (by simpa only [hE0] using hs1) hτ
    exact this
  have hcE : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 (E q)) = E q := by
    have := hτ.continuousAt.tendsto
    simp only [hE0] at this
    exact this.eventually hs2

  obtain ⟨r₁, hr₁, h₁⟩ := Metric.eventually_nhds_iff_ball.1 (hψ.eventually.and (hcE.and hLE))
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff_ball.1 hadd
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  set r := min r₁ r₂ with hrdef
  have k₁ : ∀ b ∈ Metric.ball b₀ r, ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, _ := fun b hb v hv =>
    h₁ (b, v) (Metric.ball_subset_ball (min_le_left _ _) (by rw [← ball_prod_same]; exact ⟨hb, hv⟩))
  have hex : ∀ b, ∃ ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G), b ∈ Metric.ball b₀ r →
      ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, (ε v).toMul = s b (E (b, v)) := by
    intro b
    by_cases hb : b ∈ Metric.ball b₀ r
    · obtain ⟨ε, hε⟩ := exists_addMonoidHom_eqOn_ball (g := fun v => Additive.ofMul (s b (E (b, v)))) hr
        fun v hv v' hv' => congrArg Additive.ofMul (h₂ (b, v, v') (Metric.ball_subset_ball (min_le_right _ _)
          (by rw [← ball_prod_same, ← ball_prod_same]; exact ⟨hb, hv, hv'⟩)))
      exact ⟨ε, fun _ v hv => congrArg Additive.toMul (hε v hv)⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose ε hε using hex
  obtain ⟨Q, hQ, hQo, hQ0⟩ := eventually_nhds_iff.1 (hL.eventually_analyticAt.and (hLE.and
    (((continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually (Metric.ball_mem_nhds b₀ hr)).and
      (hL.continuousAt.eventually (by rw [hL0]; exact Metric.ball_mem_nhds 0 hr)))))
  have hQb : ∀ᶠ b in 𝓝 b₀, (b, (0 : Fin g → ℂ)) ∈ Q :=
    (Continuous.tendsto (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (by fun_prop) b₀).eventually
      (hQo.mem_nhds hQ0)
  obtain ⟨B', hB', hB'o, hB'0⟩ := eventually_nhds_iff.1 (Filter.Eventually.and hB (h0.and (hQb.and
    (HolAt.eventually_near (β := fun b => b) (a := fun _ => 1) (HolAt.one hy) continuousAt_id rfl hOo hU hO))))
  refine ⟨B', fun b v => (ε b v).toMul, r, Q, L, hB'o, hB'0, fun b hb => (hB' b hb).1, hr, hQo,
    fun b z w => congrArg Additive.toMul ((ε b).map_add z w), fun b hb => ?_, fun b a ha hf hq => ?_⟩
  · obtain ⟨-, ⟨hEb, hEd⟩, hbQ, hbU, hbO⟩ := hB' b hb
    have hbr : b ∈ Metric.ball b₀ r := (hQ _ hbQ).2.2.1
    have hLb : L (b, 0) = 0 := by
      have := (hQ _ hbQ).2.1.1
      rwa [hEb] at this
    refine ⟨fun z => ?_, hbU, hbO, hbQ, ?_, hLb, (hQ _ hbQ).1, fun z hz h1 => ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_gt (‖z‖ / r)
      have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      have hz : (k : ℂ)⁻¹ • z ∈ Metric.ball (0 : Fin g → ℂ) r := by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_lt_iff₀ hk0]
        rwa [div_lt_iff₀ hr] at hk
      have hφ : AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, (k : ℂ)⁻¹ • q.2)) (b, z) :=
        analyticAt_fst.prod (analyticAt_snd.const_smul (c := (k : ℂ)⁻¹))
      have h0' := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, (k : ℂ)⁻¹ • q.2)) (v₀ := (b, z))
        (k₁ b hbr _ hz).1 hφ
      have h1 := (HolAt.pow (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) => y q.1)
        (a := fun q => s q.1 (E (q.1, (k : ℂ)⁻¹ • q.2))) h0' k)
      refine h1.congr ?_
      filter_upwards [hφ.continuousAt.eventually (prod_mem_nhds (Metric.isOpen_ball.mem_nhds hbr)
        (Metric.isOpen_ball.mem_nhds hz))] with q hq
      rw [← hε q.1 hq.1 _ hq.2, ← toMul_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hkc]
    · refine (hEd.add_const (crd U t (pt (1 : Over.mk (y b) ⟶ G)))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Fin g → ℂ) hr] with v hv
      rw [hε b hbr v hv]
      exact sub_eq_iff_eq_add.1 (k₁ b hbr v hv).2.1
    · have hz' := mem_ball_zero_iff.2 hz
      have h2 := (k₁ b hbr z hz').2
      have h3 : s b (E (b, z)) = 1 := (hε b hbr z hz').symm.trans h1
      have h4 : E (b, z) = 0 := by
        rw [← h2.1]
        simp only [h3, crd0, sub_self]
      have h5 := h2.2.1
      simp only [h4, hLb] at h5
      exact h5.symm
  · obtain ⟨-, h1, h2, h3⟩ := hQ _ hq
    refine (hε b h2 _ h3).trans ?_
    rw [h1.2]
    exact hs3 b a ha hf

end GlobalTheory.RelExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffHasMultiplicities
section
noncomputable section

namespace GlobalTheory.DetCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit

section Linear

variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]

theorem exists_bijOn_iff (W : Submodule k N) (n : ℕ) :
    (∃ v : Fin n → N, (∀ i, v i ∈ W) ∧ Set.BijOn (fun c : Fin n → k => ∑ i, c i • v i) Set.univ W) ↔
      Module.Finite k W ∧ Module.finrank k W = n := by
  constructor
  · rintro ⟨v, -, hm, hi, hs⟩
    let f : (Fin n → k) →ₗ[k] W := (Fintype.linearCombination k v).codRestrict W fun c => hm trivial
    have hf : Function.Bijective f := by
      refine ⟨fun c c' h => hi trivial trivial (congrArg Subtype.val h), fun w => ?_⟩
      obtain ⟨c, -, hc⟩ := hs w.2
      exact ⟨c, Subtype.ext hc⟩
    have e := LinearEquiv.ofBijective f hf
    exact ⟨Module.Finite.equiv e, by simpa using e.finrank_eq.symm⟩
  · rintro ⟨_, h⟩
    let b := Module.finBasisOfFinrankEq k W h
    have hb : ∀ c : Fin n → k, ∑ i, c i • (b i : N) = (b.equivFun.symm c : W) := fun c => by
      simp [Module.Basis.equivFun_symm_apply]
    refine ⟨fun i => b i, fun i => (b i).2, fun c _ => ?_, fun c _ c' _ h => ?_, fun w hw => ?_⟩
    · simp only [hb]; exact Subtype.property _
    · simp only [hb] at h; exact b.equivFun.symm.injective (Subtype.ext h)
    · exact ⟨b.equivFun ⟨w, hw⟩, trivial, by simp only [hb, LinearEquiv.symm_apply_apply]⟩

end Linear

variable {S : Scheme.{0}} {k : Type} [Field k]

variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem mem_lie_iff (t : Sp k ⟶ S) (v : epsPt t ⟶ G) :
    v ∈ Lie G t ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left :=
  ⟨fun h => congrArg (fun φ => φ.left) (show origin t ≫ v = 1 from h), fun h => Over.OverMorphism.ext h⟩

theorem isLieEigen_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen act t τ v ↔ ∃ h : v ∈ Lie G t, (⟨v, h⟩ : Lie G t) ∈ eigenspace act t τ :=
  ⟨fun h => ⟨(mem_lie_iff t v).2 h.1, fun a => Subtype.ext (Over.OverMorphism.ext (h.2 a))⟩,
    fun ⟨h, h'⟩ => ⟨(mem_lie_iff t v).1 h, fun a => congrArg (fun φ : Lie G t => φ.1.left) (h' a)⟩⟩

variable [IsCommMonObj G]

theorem comb_iff {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) (w : epsPt t ⟶ G) :
    (∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).1.left) ∧ w = (List.ofFn u).prod) ↔
      w = (comb v c).1 := by
  have key : (comb v c).1 = (List.ofFn fun i => (smulLie (c i) (v i)).1).prod := by
    rw [List.prod_ofFn]
    exact SubmonoidClass.coe_finset_prod (fun i => smulLie (c i) (v i)) Finset.univ
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain rfl : u = fun i => (smulLie (c i) (v i)).1 := funext fun i => Over.OverMorphism.ext (hu i)
    exact key.symm
  · rintro rfl
    exact ⟨fun i => (smulLie (c i) (v i)).1, fun _ => rfl, key⟩

def lieEquiv (t : Sp k ⟶ S) : Lie G t ≃ TanSp t G where
  toFun v := TanSp.mk v.1 (smT_zero_of t _ ((mem_lie_iff t _).1 v.2))
  invFun m := ⟨m.pt, (mem_lie_iff t _).2 (unit_of_smT_zero t _ m.tan)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lieEquiv_smul {t : Sp k ⟶ S} (c : k) (v : Lie G t) : lieEquiv t (smulLie c v) = c • lieEquiv t v := rfl

theorem lieEquiv_act (act : OAct O G) (t : Sp k ⟶ S) (a : O) (v : Lie G t) :
    lieEquiv t (actLie act t a v) = TanSp.act t act a (lieEquiv t v) := rfl

theorem lieEquiv_comb {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) :
    lieEquiv t (comb v c) = ∑ i, c i • lieEquiv t (v i) := by
  apply TanSp.ext
  rw [TanSp.pt_sum]
  exact SubmonoidClass.coe_finset_prod (fun i => smulLie (c i) (v i)) Finset.univ

theorem mem_eigenspace_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : Lie G t) :
    v ∈ eigenspace act t τ ↔ lieEquiv t v ∈ eigenSub (TanSp.act t act) τ := by
  rw [mem_eigenSub]
  refine forall_congr' fun a => ?_
  rw [← lieEquiv_act, ← lieEquiv_smul, (lieEquiv t).injective.eq_iff]

theorem comb_mem {act : OAct O G} {t : Sp k ⟶ S} {τ : O →+* k} {n : ℕ} {v : Fin n → Lie G t}
    (hv : ∀ i, v i ∈ eigenspace act t τ) (c : Fin n → k) : comb v c ∈ eigenspace act t τ := by
  rw [mem_eigenspace_iff, lieEquiv_comb]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((mem_eigenspace_iff act t τ _).1 (hv i))

theorem lieMult_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    LieMult act t τ n ↔ HasEigenDim act t τ n := by
  constructor
  · rintro ⟨v, hv, h⟩
    choose h1 h2 using fun i => (isLieEigen_iff act t τ _).1 (hv i)
    let v' : Fin n → Lie G t := fun i => ⟨v i, h1 i⟩
    have h' : ∀ w ∈ eigenspace act t τ, ∃! c, w = comb v' c := fun w hw => by
      have := h w.1 ((isLieEigen_iff act t τ _).2 ⟨w.2, hw⟩)
      exact (existsUnique_congr fun c => (comb_iff v' c w.1).trans Subtype.ext_iff.symm).1 this
    refine ⟨v', h2, fun c _ => comb_mem h2 c, fun c _ c' _ e => (h' _ (comb_mem h2 c)).unique rfl e,
      fun w hw => ?_⟩
    obtain ⟨c, hc, -⟩ := h' w hw
    exact ⟨c, trivial, hc.symm⟩
  · rintro ⟨v, hv, -, hi, hs⟩
    refine ⟨fun i => (v i).1, fun i => (isLieEigen_iff act t τ _).2 ⟨(v i).2, hv i⟩, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := (isLieEigen_iff act t τ _).1 hw
    obtain ⟨c, -, hc⟩ := hs h2
    refine (existsUnique_congr fun c => comb_iff v c w).2 ⟨c, (congrArg Subtype.val hc).symm, fun c' hc' => ?_⟩
    exact hi trivial trivial ((Subtype.ext hc' : (⟨w, h1⟩ : Lie G t) = comb v c').symm.trans hc.symm)

theorem hasEigenDim_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    HasEigenDim act t τ n ↔ Module.Finite k (eigenSub (TanSp.act t act) τ) ∧
      Module.finrank k (eigenSub (TanSp.act t act) τ) = n := by
  rw [← exists_bijOn_iff]
  refine (Equiv.piCongrRight fun _ => lieEquiv t).exists_congr fun v => and_congr
    (forall_congr' fun i => mem_eigenspace_iff act t τ _) ?_
  have h1 : (fun c : Fin n → k => ∑ i, c i • (Equiv.piCongrRight fun _ => lieEquiv t) v i) =
      lieEquiv t ∘ comb v := funext fun c => (lieEquiv_comb v c).symm
  have h2 : Set.BijOn (lieEquiv t) (eigenspace act t τ) (eigenSub (TanSp.act t act) τ) :=
    (lieEquiv t).bijOn (mem_eigenspace_iff act t τ · |>.symm)
  rw [h1]
  refine ⟨h2.comp, fun h => ?_⟩
  have := ((lieEquiv t).bijOn_symm.2 h2).comp h
  rwa [← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp] at this

variable {E : Type} [Field E] [NumberField E]

theorem bijective_restrict [CharZero k] :
    Function.Bijective fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
  refine ⟨fun φ ψ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => RingHom.congr_fun h a, fun τ => ?_⟩
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_splitting [CharZero k] [IsAlgClosed k] :
    ∃ _ : Fintype (𝓞 E →+* k), IsSplitting fun τ : 𝓞 E →+* k => τ := by
  classical
  let e := Equiv.ofBijective _ (bijective_restrict (E := E) (k := k))
  let F : Fintype (𝓞 E →+* k) := Fintype.ofEquiv _ e
  refine ⟨F, isSplitting_of_isDomain (σ := fun τ : 𝓞 E →+* k => τ) Function.injective_id ?_ (RingHom.id k) ?_⟩
  · rw [← NumberField.Embeddings.card E k]
    exact Fintype.card_congr e.symm
  · simpa using NumberField.discr_ne_zero E

variable [IsCMField E]

end GlobalTheory.DetCompare
end
end

