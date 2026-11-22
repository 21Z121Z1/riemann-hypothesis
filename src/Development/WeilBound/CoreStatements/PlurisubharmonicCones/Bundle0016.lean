import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0002
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalCyclotomic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0182

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenOfUnit
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uMul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem uProd {I : Type} [Fintype I] {f : I → Ω} (h : ∀ i, unitAt ξ p (f i)) : unitAt ξ p (∏ i, f i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h i).1, prod_mem fun i _ => (h i).2.1, by
    rw [← Finset.prod_inv_distrib]; exact prod_mem fun i _ => (h i).2.2⟩

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨hs0, hs⟩ := hs
  obtain ⟨ht0, ht⟩ := ht
  have h1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht, hs]
    exact Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs, ht]
    exact Submodule.mem_span_singleton_self t
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp h2
  refine ⟨div_ne_zero hs0 ht0, ?_, ?_⟩
  · have e : s / t = (u : Ω) := by
      rw [← hu, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self ht0, mul_one]
    rw [e]
    exact u.2
  · have e : (s / t)⁻¹ = (w : Ω) := by
      rw [inv_div, ← hw, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self hs0, mul_one]
    rw [e]
    exact w.2

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  obtain ⟨ht0, htl⟩ := h
  have hg : ∃ g, Λ.IsGenAt p g := by
    by_contra hno
    push_neg at hno
    have hmem : t ∈ (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p := by
      rw [htl]
      exact Submodule.mem_span_singleton_self t
    have hbot : (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p = ⊥ := by
      unfold Lat.tens
      rw [Submodule.span_eq_bot]
      rintro x ⟨s, hs, -⟩
      exact absurd (hs ()) (hno (s ()))
    rw [hbot, Submodule.mem_bot] at hmem
    exact ht0 hmem
  obtain ⟨g, hg⟩ := hg
  have hg0 : g ≠ 0 := hg.1
  have hT : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p (g ^ σ) := by
    refine ⟨zpow_ne_zero σ hg0, ?_⟩
    unfold Lat.tens
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨s, hs, rfl⟩
      have hu := uZpow (gen_unit (hs ()) hg) σ
      have e : ∏ i : Unit, s i ^ σ = (⟨(s () / g) ^ σ, hu.2.1⟩ : regAt ξ p) • g ^ σ := by
        rw [Subring.smul_def, smul_eq_mul, Fintype.prod_unique]
        show s () ^ σ = (s () / g) ^ σ * g ^ σ
        rw [div_zpow, div_mul_cancel₀ _ (zpow_ne_zero σ hg0)]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.subset_span
      exact ⟨fun _ => g, fun _ => hg, by simp⟩
  have hu := gen_unit ⟨ht0, htl⟩ hT
  have hu2 := uZpow hu σ
  have heq : (t / g ^ σ) ^ σ = t ^ σ / g := by
    rw [div_zpow, ← zpow_mul, hσ, zpow_one]
  rw [heq] at hu2
  exact gen_of_unit hg hu2

theorem gen_scale {Λ : Lat ξ Ω} {t u : Ω} (hu : u ≠ 0) (h : Λ.IsGenAt p t) : (Λ.scale u).IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero hu h.1, ?_⟩
  show (Λ p).map _ = _
  rw [h.2, Submodule.map_span, Set.image_singleton]
  rfl

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem chart_ratio {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K)
    (x : J k) : y ⟨k, x⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k x)
  dsimp only at h1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k] at h1
  · simpa using h1
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (chart_ne h b)]
  · simp

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem frame_pull {L : Lat ξ V} {r : ℕ} {b : Fin r → V} (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : LinearIndependent Ω' fun k => j (b k)) {q : Cpt ξ'} (h : genPt ξ ⤳ f q.1)
    (hreg : ∀ a ∈ regAt ξ ⟨f q.1, h⟩, i a ∈ regAt ξ' q) (hb : L.IsFrameAt b ⟨f q.1, h⟩) :
    (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) q := by
  refine ⟨hli, ?_⟩
  have hL := hb.2
  have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q.1, h⟩) (Set.range b),
      j e ∈ Submodule.span (regAt ξ' q) (Set.range fun k => j (b k)) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q) • j x := hj a x
      rw [e1]
      exact Submodule.smul_mem _ _ hx
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨h3, e, he, rfl⟩
    exact key' e (by rw [← hL]; exact he)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨h, b k, ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

theorem deg_pull {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {Λ' : I → Lat ξ' Ω'} {u : I → Ω'} (hu : ∀ τ, u τ ≠ 0)
    (hd : Dominates ξ' ξ f i)
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hΛ : ∀ τ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (Λ τ).IsGenAt ⟨f q.1, h⟩ t ∧ (Λ' τ).IsGenAt q (u τ * i t))
    {K' : Type} [Fintype K'] {J' : K' → Type} {y' : (Σ k, J' k) → Ω'} {bk : K → K'} {bx : ∀ k, J k ≃ J' (bk k)}
    (hbk : Function.Injective bk) (hy : ∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) {a : K → ℤ} {a' : K' → ℤ}
    (ha : ∀ k, a' (bk k) = a k) (ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0) {e₀ : Ω}
    (h : (Lat.tens Λ fun _ => -1).IsDegOn Set.univ y a e₀) :
    ((Lat.tens Λ' fun _ => -1).scale (∏ τ, u τ)).IsDegOn Set.univ y' a' (i e₀) := by
  refine ⟨(map_ne_zero i).2 h.1, fun q _ c' hc' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  obtain ⟨c, hc⟩ := hcov ⟨f q.1, hq⟩
  choose t ht ht' using fun τ => hΛ τ q hq
  have g1 := uMap hreg (gen_unit (deg_gen h hc) (Flag.tens_gen Λ (fun _ => -1) _ t ht))
  have g2 := gen_scale (Finset.prod_ne_zero_iff.2 fun τ _ => hu τ : ∏ τ, u τ ≠ 0)
    (Flag.tens_gen Λ' (fun _ => -1) q _ ht')
  have g3 : ∀ k, unitAt ξ' q (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) := fun k => by
    refine ⟨div_ne_zero (chart_ne hc' _) ((map_ne_zero i).2 (chart_ne hc k)), ?_, ?_⟩
    · have := hreg _ (chart_ratio hc k ((bx k).symm (c' (bk k))))
      rwa [map_div₀, ← hy, Equiv.apply_symm_apply] at this
    · rw [inv_div, ← hy]
      exact chart_ratio hc' _ _
  have g4 := uMul (uProd fun k => uZpow (g3 k) (a k)) g1
  have e1 : ∏ k', y' ⟨k', c' k'⟩ ^ a' k' = ∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k := by
    symm
    refine Fintype.prod_of_injective bk hbk _ _ (fun k' hk' => ?_) fun k => by rw [ha]
    rw [ha' k' hk', zpow_zero]
  have e2 : (∏ τ, u τ) * ∏ τ, (u τ * i (t τ)) ^ (-1 : ℤ) = i (∏ τ, t τ ^ (-1 : ℤ)) := by
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := hu τ
    rw [map_zpow₀, zpow_neg_one, zpow_neg_one, mul_inv, mul_inv_cancel_left₀ this]
  rw [e2] at g2
  refine (gen_of_unit (s := (∏ k', y' ⟨k', c' k'⟩ ^ a' k') * i e₀) g2 ?_).2
  convert g4 using 1
  have e3 : i (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    (map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k))
  have e4 : ∏ k, (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) ^ a k =
      (∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k) / i (∏ k, y ⟨k, c k⟩ ^ a k) := by
    rw [map_prod, ← Finset.prod_div_distrib]
    simp only [div_zpow, map_zpow₀]
  rw [e1, e4, map_div₀, map_mul, ← mul_div_assoc, ← _root_.mul_assoc, div_mul_cancel₀ _ e3]

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.InFibreLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

theorem exists_prime_mem {O : Type} [CommRing O] (P : Ideal O) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (h : (n : O) ∈ P) : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : O) ∈ P := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact absurd (by simpa using h) ((Ideal.ne_top_iff_one _).1 hP.ne_top)
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨r, h1, h2, h3⟩ := ih (right_ne_zero_of_mul hn) h
      exact ⟨r, h1, h2.mul_left _, h3⟩

theorem lie_cast {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {w w' : Sp F ⟶ X} (h : w = w') (ML : LieModel G w V) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End F V) (hact : ML.IsActOf act ρ) :
    ∃ MC : LieModel G w' V, (∀ x, (MC.pt x).left = (ML.pt x).left) ∧
      (∀ e x, M.ValAt w' e (MC.pt x) ↔ M.ValAt w e (ML.pt x)) ∧ MC.IsActOf act ρ := by
  subst h
  exact ⟨ML, fun _ => rfl, fun _ _ => Iff.rfl, hact⟩

theorem centre_loc {X : Scheme.{0}} {O : Type} [CommRing O] (z : Sp O ⟶ X) (P : Ideal O) [hP : P.IsPrime] :
    centre (spMap (algebraMap O (Localization.AtPrime P)) ≫ z) = z (⟨P, hP⟩ : PrimeSpectrum O) := by
  have e : (spMap (algebraMap O (Localization.AtPrime P))) (IsLocalRing.closedPoint (Localization.AtPrime P)) =
      (⟨P, hP⟩ : PrimeSpectrum O) := by
    apply PrimeSpectrum.ext
    show (IsLocalRing.maximalIdeal _).comap (algebraMap O (Localization.AtPrime P)) = P
    exact Localization.AtPrime.comap_maximalIdeal
  show z ((spMap (algebraMap O (Localization.AtPrime P))) (IsLocalRing.closedPoint _)) = _
  rw [e]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X)

omit [∀ k, Fintype (J k)] in
theorem inFibre_loc (P : Ideal (𝓞 L)) [P.IsPrime] {p : ℕ} (hp : (p : 𝓞 L) ∈ P) :
    InFibre 𝔐.ξ p ⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime P)) ≫ z), 𝔐.all _⟩ := fun hu => by
  have h := (PositivityTheory.HtPt.Gh.unitAt_centre_iff 𝔐.tie.gen _ (𝔐.all _) p).1 hu
  rw [← map_natCast (algebraMap (𝓞 L) (Localization.AtPrime P))] at h
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).1 h hp

set_option maxHeartbeats 800000 in

theorem loc {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
    (ML : LieModel 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (ρ : 𝓞 E →+* Module.End L V)
    (hact : ML.IsActOf 𝔐.t.act.act ρ) (σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L))
    (hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)))
    (hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s)) (κ : ℕ → Ω) (k : ℕ → 𝓞 L)
    (hκ : ∀ p ∈ S, HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p (κ p) ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (κ p) (algebraMap (𝓞 L) L (k p)))
    (hdisc : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) (s : CMType H ⊕ CMType H)
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] (cc : Localization.AtPrime P →+* L)
    (hc : cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L) :
    (∀ x ∈ eigSp ρ ((algebraMap (𝓞 L) L).comp (σ₀ s)),
      (∃ v : epsAt z ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G z v ∧
        (ML.pt x).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) →
      ∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}) ∧
    ∀ x, (∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}) → ∀ d ∈ differentIdeal ℤ (𝓞 E),
      (∏ p ∈ S, k p) • σ₀ s d • x ∈ eigSp ρ ((algebraMap (𝓞 L) L).comp (σ₀ s)) ∧
      ∃ w : epsAt (spMap (algebraMap (𝓞 L) (Localization.AtPrime P)) ≫ z) ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G _ w ∧
        (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)).left = spMap (dualMap cc) ≫ w.left := by
  classical
  have hξ := 𝔐.tie.gen
  let A := Localization.AtPrime P
  letI : Algebra A L := cc.toAlgebra
  have hc' : ∀ a, algebraMap A L (algebraMap (𝓞 L) A a) = algebraMap (𝓞 L) L a := fun a => RingHom.congr_fun hc a
  haveI : IsScalarTower (𝓞 L) A L := IsScalarTower.of_algebraMap_eq fun a => (hc' a).symm
  letI : Module A V := Module.compHom V cc
  haveI : IsScalarTower A L V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower (𝓞 L) A V := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul L (algebraMap (𝓞 L) A r) x, hc', algebraMap_smul]
  haveI : IsFractionRing A L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A L
  have inj := IsFractionRing.injective A L
  let zA : Sp A ⟶ 𝔐.X := spMap (algebraMap (𝓞 L) A) ≫ z
  have hzL : spMap (algebraMap (𝓞 L) L) ≫ z = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ zA := by
    rw [← hc, ← Category.assoc]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  obtain ⟨MC, hM1, hM2, hM3⟩ := lie_cast 𝔐.M hzL ML _ ρ hact
  have hq : (⟨centre zA, 𝔐.all _⟩ : Cpt 𝔐.ξ) = ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ :=
    Subtype.ext (centre_loc z P)
  have hmv : ∀ (e : 𝔐.Li) (q q' : Cpt 𝔐.ξ), q = q' → e ∈ 𝔐.V s q → e ∈ 𝔐.V s q' := by
    rintro e _ _ rfl h; exact h
  have hfib : ∀ x, x ∈ 𝔐.M.fibAt (𝔐.V s) zA MC ↔ ∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L)
      {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := by
    intro x
    have e1 : 𝔐.M.fibAt (𝔐.V s) zA MC = Submodule.span A
        {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
          𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := by
      unfold LieModel.fibAt
      congr 1
      ext w
      exact ⟨fun ⟨_, e, h1, h2⟩ => ⟨e, hmv e _ _ hq h1, (hM2 _ _).1 h2⟩,
        fun ⟨e, h1, h2⟩ => ⟨𝔐.all _, e, hmv e _ _ hq.symm h1, (hM2 _ _).2 h2⟩⟩
    rw [e1, IsLocalization.mem_span_iff P.primeCompl]
    have e2 : ∀ (t : P.primeCompl) (u : V), (t : 𝓞 L) • IsLocalization.mk' A (1 : 𝓞 L) t • u = u := fun t u => by
      rw [← algebraMap_smul A (t : 𝓞 L), smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    constructor
    · rintro ⟨u, hu, t, rfl⟩
      exact ⟨t, t.2, by rwa [e2]⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨_, h, ⟨t, ht⟩, by rw [smul_comm]; exact (e2 ⟨t, ht⟩ x).symm⟩
  have hlat := GlobalTheory.T.lie_lattice_eval_fraction_field 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M A zA L V MC hξ 𝔐.t.semi.smooth (𝔐.all _) (𝔐.all _)
  have hval : ∀ {a : Ω} {r : A} {n : 𝓞 L}, ValAt 𝔐.ξ zA a r →
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a (algebraMap (𝓞 L) L n) →
      ValAt 𝔐.ξ zA a (algebraMap (𝓞 L) A n) := fun {a r n} h1 h2 => by
    have h3 := LieTangent.valAt_base hξ (algebraMap A L) h1
    rw [← hzL] at h3
    have h4 := LieTangent.valAt_unique hξ h3 h2
    rw [← hc'] at h4
    rwa [← inj h4]
  let σA : CMType H ⊕ CMType H → (𝓞 E →+* A) := fun s => (algebraMap (𝓞 L) A).comp (σ₀ s)
  have hσA : ∀ s a, ValAt 𝔐.ξ zA (𝔐.emb s a) (σA s a) := fun s a => by
    obtain ⟨r, hr⟩ := emb_value 𝔐 zA s a
    exact hval hr (hσ s a)
  have hσe : ∀ s, (algebraMap A L).comp (σA s) = (algebraMap (𝓞 L) L).comp (σ₀ s) := fun s =>
    RingHom.ext fun a => hc' _
  have main : 𝔐.M.fibAt 𝔐.M.lat zA MC ⊓ (eigSp ρ ((algebraMap A L).comp (σA s))).restrictScalars A ≤
      𝔐.M.fibAt (𝔐.V s) zA MC ∧ ∀ w ∈ 𝔐.M.fibAt (𝔐.V s) zA MC, ∀ d ∈ differentIdeal ℤ (𝓞 E),
      algebraMap (𝓞 L) A (∏ p ∈ S, k p) • σA s d • w ∈
        𝔐.M.fibAt 𝔐.M.lat zA MC ⊓ (eigSp ρ ((algebraMap A L).comp (σA s))).restrictScalars A := by
    by_cases hex : ∃ p ∈ S, (p : 𝓞 L) ∈ P
    · obtain ⟨p, hpS, hp⟩ := hex
      have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 (𝔐.S_prime p hpS).ne_zero
      have hP0 : P ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hp)
      haveI : IsDiscreteValuationRing A :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP0 A
      obtain ⟨v, hv, hv1⟩ := exists_val A L
      have hvp : v (p : L) < 1 := by
        have := hv1 (algebraMap (𝓞 L) A p) fun h => (IsLocalization.AtPrime.isUnit_to_map_iff A P _).1 h hp
        rwa [hc', map_natCast] at this
      obtain ⟨h1, h2, h3⟩ := hκ p hpS
      obtain ⟨r, hr⟩ := exists_value zA (𝔐.all _) (h2 _ (inFibre_loc 𝔐 z P hp)).1
      obtain ⟨a1, a2⟩ := on_S 𝔐 zA MC ρ hM3 hpS (κ p) h1 h2 v hv hvp s (σA s) (hσA s) _ (hval hr h3)
      refine ⟨a1, fun w hw d hd => ?_⟩
      rw [← Finset.prod_erase_mul S k hpS, map_mul, mul_smul]
      exact Submodule.smul_mem _ _ (a2 w hw d hd)
    · have hun : ∀ n : ℕ, (n : 𝓞 L) ∉ P → IsUnit (n : A) := fun n hn => by
        rw [← map_natCast (algebraMap (𝓞 L) A)]
        exact IsLocalization.map_units A (⟨n, hn⟩ : P.primeCompl)
      have e := off_S 𝔐 zA MC ρ hM3 σA hσA (by simpa only [hσe] using hinj)
        (fun p hp => hun p fun h => hex ⟨p, hp, h⟩)
        (hun _ fun h => by
          obtain ⟨r, h1, h2, h3⟩ := exists_prime_mem P _ (Int.natAbs_ne_zero.2 (discr_ne_zero E)) h
          exact hex ⟨r, hdisc r h1 (Int.natCast_dvd.2 h2), h3⟩) s
      refine ⟨e.ge, fun w hw d _ => ?_⟩
      rw [← e]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw)
  rw [hσe] at main
  refine ⟨fun x hx ⟨v, hv, hxv⟩ => (hfib x).1 (main.1 ⟨(hlat x).2 ?_, hx⟩), fun x hx d hd => ?_⟩
  · refine ⟨LieCarrier.epsHom (algebraMap (𝓞 L) A) z zA rfl ≫ v, LieFib.isTanAt_epsHom _ _ _ _ _ hv, ?_⟩
    rw [hM1, hxv, ← hc]
    exact (congrArg (· ≫ v.left) (LieFib.spec_dualMap_comp _ cc)).trans (Category.assoc _ _ _)
  · obtain ⟨h1, h2⟩ := main.2 x ((hfib x).2 hx) d hd
    have e : algebraMap (𝓞 L) A (∏ p ∈ S, k p) • σA s d • x = (∏ p ∈ S, k p) • σ₀ s d • x := by
      rw [algebraMap_smul]
      exact congrArg _ (algebraMap_smul A (σ₀ s d) x)
    rw [e] at h1 h2
    obtain ⟨w, hw, hw'⟩ := (hlat _).1 h1
    exact ⟨h2, w, hw, (hM1 _).symm.trans hw'⟩

end LevelTowerAlt.LocalPrimeBound
end
end

