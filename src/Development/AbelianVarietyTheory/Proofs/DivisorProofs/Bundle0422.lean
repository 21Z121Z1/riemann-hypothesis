import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPTypicalTangent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0012
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OpenDim

theorem ringKrullDim_affineOpen (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ d : ℕ, ringKrullDim Γ(Y, U) = d ∧ Algebra.trdeg F Y.functionField = d := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη =
      Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower F Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul F Γ(Y, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(Y, U)).injective
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  exact ⟨d, h₁, (trdeg_eq_of_isAlgebraic_top F Γ(Y, U) Y.functionField).trans h₂⟩

theorem topologicalKrullDim_open (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] (V : Y.Opens) (hne : (V : Set Y).Nonempty) :
    topologicalKrullDim (V : Set Y) = topologicalKrullDim Y := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra

  have chart : ∀ (V : Y.Opens) (x : Y), x ∈ V → ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V :=
    fun V x hx ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
      exact ⟨U, hU, hxU, hUV⟩
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨U₀, hU₀, hx₀U₀, -⟩ := chart V x₀ hx₀
  obtain ⟨d₀, -, hd₀⟩ := ringKrullDim_affineOpen F f hU₀ ⟨x₀, hx₀U₀⟩
  have affDim : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim (U : Set Y) = d₀ := fun U hU hUne ↦ by
    obtain ⟨d, h₁, h₂⟩ := ringKrullDim_affineOpen F f hU hUne
    obtain rfl : d = d₀ := by exact_mod_cast h₂.symm.trans hd₀
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have openDim : ∀ V : Y.Opens, (V : Set Y).Nonempty → topologicalKrullDim (V : Set Y) = d₀ :=
    fun V hV ↦ topologicalKrullDim_eq_of_forall_exists_isOpen hV fun x hx ↦ by
      obtain ⟨U, hU, hxU, hUV⟩ := chart V x hx
      refine ⟨U, U.isOpen, hxU, ?_⟩
      rw [Set.inter_eq_left.mpr hUV]
      exact affDim U hU ⟨x, hxU⟩
  have htop := openDim ⊤ ⟨x₀, trivial⟩
  rw [openDim V ⟨x₀, hx₀⟩, ← htop]
  exact (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Z := ((⊤ : Y.Opens) : Set Y)) (by simp))

theorem topologicalKrullDim_eq_of_isIso_restrict : ∀ (F : Type) [Field F] (W W' : Scheme.{0})
    [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W),
    LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens,
    (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  intro F _ W W' _ _ p q h hp hq _ U hU hiso
  have hsurj : Function.Surjective (h ∣_ U) := (h ∣_ U).surjective
  have e₁ : topologicalKrullDim (U : Set W) = topologicalKrullDim (h ⁻¹ᵁ U) := by
    refine topologicalKrullDim_eq_of_isEmbedding ((h ∣_ U) ≫ U.ι).isOpenEmbedding.isEmbedding ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
  have e₂ : topologicalKrullDim ((h ⁻¹ᵁ U : W'.Opens) : Set W') =
      topologicalKrullDim (h ⁻¹ᵁ U) :=
    topologicalKrullDim_eq_of_isEmbedding (h ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding
      (Scheme.Opens.range_ι _)
  have hne : ((h ⁻¹ᵁ U : W'.Opens) : Set W').Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨y, -⟩ := hsurj ⟨u, hu⟩
    exact ⟨(h ⁻¹ᵁ U).ι y, by rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩⟩
  rw [← topologicalKrullDim_open F q (h ⁻¹ᵁ U) hne, ← topologicalKrullDim_open F p U hU, e₁, e₂]

end GlobalTheory.OpenDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportAlg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.HT.TateTransportO

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

theorem transport_alg :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p)
    {R k k' QR Q Q' : Type} [CommRing R] [Field k] [Field k'] [Group QR] [Group Q] [Group Q'],
    (∀ a b : QR, a * b = b * a) →
    ∀ (actR : D.O → QR → QR) (act : D.O → Q → Q) (act' : D.O → Q' → Q')
    (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → k'ˣ → Prop)
    (ρ : QR →* Q) (ρ' : QR →* Q') (φ : Rˣ →* kˣ) (φ' : Rˣ →* k'ˣ),
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q', x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ' g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ u = φ v → u = v) →
    (∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ φ u = z) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ' u = φ' v → u = v) →
    (∀ c g h, actR c (g * h) = actR c g * actR c h) →
    (∀ c g, ρ (actR c g) = act c (ρ g)) → (∀ c g, ρ' (actR c g) = act' c (ρ' g)) →
    (∀ c, act' c 1 = 1) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 →
      ∃ u : Rˣ, u ^ n = 1 ∧ e n (ρ g) (ρ h) (φ u) ∧ e' n (ρ' g) (ρ' h) (φ' u)) →
    (∀ n, 0 < n → n.Coprime p → ∀ x y c c', e n x y c → e n x y c' → c = c') →
    ∀ (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e),
    ∃ I' : GlobalTheory.UPel.HT.TateIsoO D k' Q' act' e', ∀ n, 0 < n → n.Coprime p → ∀ a (g : QR), g ^ n = 1 →
      ρ g = I.ev n a → ρ' g = I'.ev n a := by
  intro p _ D R k k' QR Q Q' _ _ _ _ _ _ hcomm actR act act' e e' ρ ρ' φ φ' hρi hρs hρ'i hρ's hφi hφs hφ'i
    hactR hρact hρ'act hact'1 hpair huniq I
  obtain ⟨L, hL⟩ := exists_torsLift p ρ hρi
  obtain ⟨W, hW⟩ := exists_torsLift p φ hφi
  have hLx : ∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → L x ^ n = 1 ∧ ρ (L x) = x := by
    intro n hn hnp x hx
    obtain ⟨g, hg, rfl⟩ := hρs n hn hnp x hx
    rw [hL n hn hnp g hg]; exact ⟨hg, rfl⟩
  have hWx : ∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → W z ^ n = 1 ∧ φ (W z) = z := by
    intro n hn hnp z hz
    obtain ⟨u, hu, rfl⟩ := hφs n hn hnp z hz
    rw [hW n hn hnp u hu]; exact ⟨hu, rfl⟩
  have hLmul : ∀ n, 0 < n → n.Coprime p → ∀ x y : Q, x ^ n = 1 → y ^ n = 1 → L (x * y) = L x * L y := by
    intro n hn hnp x y hx hy
    obtain ⟨hx1, hx2⟩ := hLx n hn hnp x hx
    obtain ⟨hy1, hy2⟩ := hLx n hn hnp y hy
    have := hL n hn hnp (L x * L y)
      (by rw [(show Commute (L x) (L y) from hcomm _ _).mul_pow, hx1, hy1, _root_.one_mul])
    rwa [map_mul, hx2, hy2] at this
  have hevt : ∀ n, 0 < n → n.Coprime p → ∀ a, I.ev n a ^ n = 1 :=
    fun n hn hnp a => (I.onto n hn hnp _).2 ⟨a, rfl⟩
  have hζt : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 :=
    fun n hn hnp => (I.ζ_prim n hn hnp).pow_eq_one
  have hactR1 : ∀ c, actR c 1 = 1 := fun c => by
    have := hactR c 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have hactRpow : ∀ c g (n : ℕ), actR c (g ^ n) = actR c g ^ n := by
    intro c g n
    induction n with
    | zero => simp [hactR1]
    | succ n ih => rw [pow_succ, hactR, ih, pow_succ]
  have hLact : ∀ n, 0 < n → n.Coprime p → ∀ c x, x ^ n = 1 → L (act c x) = actR c (L x) := by
    intro n hn hnp c x hx
    obtain ⟨h1, h2⟩ := hLx n hn hnp x hx
    have := hL n hn hnp (actR c (L x)) (by rw [← hactRpow, h1, hactR1])
    rwa [hρact, h2] at this
  refine ⟨{ ζ := fun n => φ' (W (I.ζ n)),
             ζ_prim := ?_,
             ζ_pow := ?_,
             ev := fun n a => if 0 < n ∧ n.Coprime p then ρ' (L (I.ev n a)) else 1,
             add := ?_,
             lin := ?_,
             ker := ?_,
             onto := ?_,
             tower := ?_,
             isom := ?_ }, ?_⟩
  · intro n hn hnp
    obtain ⟨hw1, hw2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    refine ⟨by rw [← map_pow, hw1, map_one], fun l hl => ?_⟩
    rw [← map_pow] at hl
    have : W (I.ζ n) ^ l = 1 := hφ'i n hn hnp _ _
      (by rw [← pow_mul, mul_comm, pow_mul, hw1, one_pow]) (one_pow n) (by rw [hl, map_one])
    exact (I.ζ_prim n hn hnp).dvd_of_pow_eq_one l (by rw [← hw2, ← map_pow, this, map_one])
  · intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    obtain ⟨a1, a2⟩ := hWx (n * m) (Nat.mul_pos hn hm) hnm _ (hζt _ (Nat.mul_pos hn hm) hnm)
    obtain ⟨b1, b2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    show φ' (W (I.ζ (n * m))) ^ m = φ' (W (I.ζ n))
    rw [← map_pow, hφi n hn hnp (W (I.ζ (n * m)) ^ m) (W (I.ζ n))
      (by rw [← pow_mul, mul_comm m n, a1]) b1 (by rw [map_pow, a2, b2, I.ζ_pow n m hn hm hnm])]
  · intro n a b
    split_ifs with h
    · rw [I.add, hLmul n h.1 h.2 _ _ (hevt n h.1 h.2 a) (hevt n h.1 h.2 b), map_mul]
    · rw [_root_.mul_one]
  · intro n c a
    split_ifs with h
    · rw [I.lin, hLact n h.1 h.2 c _ (hevt n h.1 h.2 a), hρ'act]
    · rw [hact'1]
  · intro n hn hnp a
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    rw [← I.ker n hn hnp a]
    obtain ⟨h1, h2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    constructor
    · intro h
      have := hρ'i n hn hnp _ 1 h1 (one_pow n) (by rw [h, map_one])
      rw [← h2, this, map_one]
    · intro h
      rw [h, ← map_one ρ, hL n hn hnp 1 (one_pow n), map_one]
  · intro n hn hnp y
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    constructor
    · intro hy
      obtain ⟨g, hg1, rfl⟩ := hρ's n hn hnp y hy
      obtain ⟨a, ha⟩ := (I.onto n hn hnp (ρ g)).1 (by rw [← map_pow, hg1, map_one])
      exact ⟨a, by rw [ha, hL n hn hnp g hg1]⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (hLx n hn hnp _ (hevt n hn hnp a)).1, map_one]
  · intro n m hn hm hnm a
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    have hnm0 : 0 < n * m := Nat.mul_pos hn hm
    have hg1 : 0 < n * m ∧ (n * m).Coprime p := ⟨hnm0, hnm⟩
    have hg2 : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg1, if_pos hg2]
    obtain ⟨h1, h2⟩ := hLx (n * m) hnm0 hnm _ (hevt _ hnm0 hnm a)
    have := hL n hn hnp (L (I.ev (n * m) a) ^ m) (by rw [← pow_mul, mul_comm m n, h1])
    rw [map_pow, h2, I.tower n m hn hm hnm] at this
    rw [← map_pow, ← this]
  · intro n hn hnp a b
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    obtain ⟨ga1, ga2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    obtain ⟨gb1, gb2⟩ := hLx n hn hnp _ (hevt n hn hnp b)
    obtain ⟨u, hu, he, he'⟩ := hpair n hn hnp _ _ ga1 gb1
    rw [ga2, gb2] at he
    obtain ⟨w1, w2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    have hk := huniq n hn hnp _ _ _ _ he (I.isom n hn hnp a b)
    have hu' : u = W (I.ζ n) ^ (2 * D.EF a b) := hφi n hn hnp _ _ hu
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm (2 * D.EF a b), zpow_mul, zpow_natCast, w1, one_zpow])
      (by rw [hk, map_zpow, w2])
    rw [hu', map_zpow] at he'
    exact he'
  · intro n hn hnp a g hg hρg
    have hgd : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hgd]
    rw [← hρg, hL n hn hnp g hg]

end GlobalTheory.UPel.HT.TateTransportO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTensorWidePullbackLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

theorem widePullbackCone_congr {X Y W : Scheme.{0}} {n : ℕ} (f : Y ⟶ X) (b : W ⟶ X)
    (π π' : Fin n → (W ⟶ Y)) (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b) (e : π = π')
    (H : Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => f) b π h))) :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => f) b π' h')) := by
  subst e
  exact H

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def l3 : Fin (2 + 1) → (B →+* B ⊗[A] (B ⊗[A] B)) :=
  ![(Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom,
    ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom,
    ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom]

theorem triple_tensor_inclusion_comp_algebraMap : ∀ i, (l3 A B i).comp (algebraMap A B) = algebraMap A (B ⊗[A] (B ⊗[A] B)) := by
  intro i
  fin_cases i <;>
  · simp only [l3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
    rw [AlgHom.toRingHom_eq_coe]
    first
    | exact AlgHom.comp_algebraMap _
    | exact AlgHom.comp_algebraMap (_ : B →ₐ[A] B ⊗[A] (B ⊗[A] B))
    | (ext a; simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def])

theorem tmul_tmul_eq (x y z : B) :
    x ⊗ₜ[A] (y ⊗ₜ[A] z) = l3 A B 0 x * l3 A B 1 y * l3 A B 2 z := by
  simp [l3, Algebra.TensorProduct.tmul_mul_tmul]

theorem triple_tensor_ring_hom_ext {T : Type} [CommRing T] (v w : B ⊗[A] (B ⊗[A] B) →+* T)
    (h : ∀ i, v.comp (l3 A B i) = w.comp (l3 A B i)) : v = w := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | tmul x s =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [TensorProduct.tmul_add, map_add, map_add, hp, hq]
    | tmul y z =>
      rw [tmul_tmul_eq, map_mul, map_mul, map_mul, map_mul]
      have h0 := RingHom.congr_fun (h 0) x
      have h1 := RingHom.congr_fun (h 1) y
      have h2 := RingHom.congr_fun (h 2) z
      simp only [RingHom.comp_apply] at h0 h1 h2
      rw [h0, h1, h2]

theorem tensor3_univ (T : Type) [CommRing T] (g : Fin (2 + 1) → (B →+* T)) (c : A →+* T)
    (hg : ∀ i, (g i).comp (algebraMap A B) = c) :
    ∃! u : B ⊗[A] (B ⊗[A] B) →+* T, u.comp (algebraMap A _) = c ∧ ∀ i, u.comp (l3 A B i) = g i := by
  letI : Algebra A T := c.toAlgebra
  let G : Fin (2 + 1) → (B →ₐ[A] T) := fun i =>
    { g i with
      commutes' := fun a => by
        have := RingHom.congr_fun (hg i) a
        simpa [RingHom.algebraMap_toAlgebra] using this }
  let inner : B ⊗[A] B →ₐ[A] T := Algebra.TensorProduct.lift (G 1) (G 2) (fun _ _ => Commute.all _ _)
  let U : B ⊗[A] (B ⊗[A] B) →ₐ[A] T := Algebra.TensorProduct.lift (G 0) inner (fun _ _ => Commute.all _ _)
  have hU : ∀ i, U.toRingHom.comp (l3 A B i) = g i := by
    intro i
    fin_cases i <;>
    · ext x
      simp [l3, U, inner, G]
  refine ⟨U.toRingHom, ⟨?_, hU⟩, ?_⟩
  · ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl
  · rintro u ⟨-, hu⟩
    exact triple_tensor_ring_hom_ext A B _ _ (fun i => (hu i).trans (hU i).symm)

theorem spec_tensor3_isLimit : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (2 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (GlobalTheory.CechOne.y2 A B)
      (GlobalTheory.CechOne.hy2 A B))) := by
  intro A B _ _ _
  have H := GlobalTheory.spec_widePushout_isLimit (2 + 1) A B (B ⊗[A] (B ⊗[A] B)) (algebraMap A B)
    (algebraMap A _) (l3 A B) (triple_tensor_inclusion_comp_algebraMap A B) (fun T _ g c hg => tensor3_univ A B T g c hg)
  refine widePullbackCone_congr _ _ _ _ _ _ ?_ H
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CechOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBases
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.TypicalCurveBases

theorem typical_curves_tangent_and_bases : TypicalCurveEigenspace ∧ TypicalCurveBasisExists :=
  have h2 : TypicalCurveEigenspace :=
    GlobalTheory.TypicalCurve.typicalCurves_of_type_of_typical_tangents GlobalTheory.PTypicalTangent.exists_pTypical_tangent
  ⟨h2, GlobalTheory.typicalBasis_coordinates h2⟩

end GlobalTheory.TypicalCurveBases
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDivLeOneCofinite
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.LocGenVal

theorem valuation_div_le_one_cofinite : ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (u : K),
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ a : K, Formalism.L2.LamCM.IsLocGen p a I → u ≠ 0 →
      p.valuation K (a / u) ≤ 1 := by
  intro K _ _ I u
  classical
  have h1 := Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K) I)
  have h2 := Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (K := K) (FractionalIdeal.spanSingleton (𝓞 K)⁰ u))
  refine ⟨(h1.union h2).toFinset, ?_⟩
  intro p hp a ha hu
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
  obtain ⟨hpI, hpu⟩ := hp
  have hau : a / u ≠ 0 := div_ne_zero ha.1 hu
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha.1
  have hsu : FractionalIdeal.spanSingleton (𝓞 K)⁰ u ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hu
  have hc : FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / u)) = 0 := by
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.count_mul K p hsa (inv_ne_zero hsu), FractionalIdeal.count_inv, ha.2, hpI, hpu]
    simp
  rw [Formalism.L2.LamCM.valuation_eq_exp_neg_count p hau, hc, neg_zero, WithZero.exp_zero]

end GlobalTheory.LocGenVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VmulNeZero
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.SepGL

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by
  intro N _ τ α β h
  rcases subsingleton_or_nontrivial (ZMod N) with hs | hs
  · exact Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _
  · have key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β := by
      intro i
      have h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0 := by
        intro h1
        have := congrFun h1 i
        simp at this
      exact GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have := congrFun (key i) j
    simpa [vmul, Matrix.single_vecMul] using this

end GlobalTheory.WpFam.SepGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChangeStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sign_iMulti_D_chart_change : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i : Fin (d + 1), ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) = ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  first | (exact @GlobalTheory.PD.volume_chart_change) | (exact GlobalTheory.PD.volume_chart_change) | (intros; apply GlobalTheory.PD.volume_chart_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_value_q_expansion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionB.main | exact GlobalTheory.WpFam.ExpansionB.main | (intros; apply GlobalTheory.WpFam.ExpansionB.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFormulaFourierQuadraticCharacterStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_fourier_quadratic_character : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s → (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x, four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  first | exact @GlobalTheory.KSp.WeilFormula.weil_formula | exact GlobalTheory.KSp.WeilFormula.weil_formula | (intros; apply GlobalTheory.KSp.WeilFormula.weil_formula <;> assumption)
end

