import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondOnto
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev.Onto

theorem range_sp_subset_iff {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) (U : Set X) :
    Set.range f ⊆ U ↔ ∃ t, f t ∈ U := by
  haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))
  constructor
  · intro h
    exact ⟨default, h ⟨default, rfl⟩⟩
  · rintro ⟨t, ht⟩ _ ⟨t', rfl⟩
    rwa [Subsingleton.elim t' t]

theorem range_sp_subset_compl {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) (U : Set X) :
    Set.range f ⊆ Uᶜ ↔ ¬ Set.range f ⊆ U := by
  haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))
  rw [range_sp_subset_iff, range_sp_subset_iff]
  constructor
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩
    rw [Subsingleton.elim t' t] at ht'
    exact ht ht'
  · intro h
    exact ⟨default, fun h' => h ⟨default, h'⟩⟩

end GlobalTheory.UPel.HT.EtLev.Onto

namespace GlobalTheory.UPel.HT.EtLev

open GlobalTheory.UPel.HT.EtLev.Onto

theorem clopenCond_onto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hker
  haveI := hKf; haveI := hKe; haveI := hZf; haveI := hZe
  have hkc : ∀ (T T' : Over S) (f : T ⟶ T') (g : T' ⟶ o.A),
      (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
      ∀ c ∈ w0 ^ r, (f ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T T' f g hg c hc
    rw [Category.assoc, hg c hc, MonObj.comp_one]
  have hetk : ∀ a, ∀ c ∈ w0 ^ r, et a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun a c hc => by
    rw [← hlin]
    exact hker _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  have huniq : ∀ (T : Over S) (y y' : T ⟶ K), y ≫ κ = y' ≫ κ → y = y' := fun T y y' h =>
    (hrep T (y' ≫ κ) (hkc _ _ y' κ hκ)).unique h rfl
  choose lam hlam using fun a => (hrep Z (et a) (hetk a)).exists
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, _, q, hq⟩ := LevCover.exists_finite_mod D.La (pow_pos (Fact.out : p.Prime).pos r)
  have hlamq : ∀ a a', q a = q a' → lam a = lam a' := by
    intro a a' h
    obtain ⟨c, rfl⟩ := hq a a' h
    have hm : p ^ r • c ∈ wSub D w0 r := by
      refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
      rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply huniq
    rw [hlam, hlam, hadd, hker _ hm, _root_.mul_one]
  have hfin : (Set.range lam).Finite := by
    refine (Set.finite_range fun j : Set.range q => lam j.2.choose).subset ?_
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨q a, Set.mem_range_self a⟩, ?_⟩
    exact hlamq _ _ (Classical.choose_spec (Set.mem_range_self (f := q) a))
  obtain ⟨hPf, hPe⟩ := LevCover.finiteEtale_tensor Z K
  haveI := hPf; haveI := hPe
  let U : (Z ⟶ K) → (Z ⊗ K).left.Opens := fun l => (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose
  have hU : ∀ l, IsClosed (U l : Set (Z ⊗ K).left) ∧ ∀ (T' : Over S) (h : T' ⟶ Z ⊗ K),
      h ≫ snd Z K = h ≫ fst Z K ≫ l ↔ Set.range h.left ⊆ U l := fun l =>
    (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose_spec
  let C : Set (Z ⊗ K).left := ⋂ l ∈ Set.range lam, (U l : Set (Z ⊗ K).left)ᶜ
  have hCo : IsOpen C := hfin.isOpen_biInter fun l _ => (hU l).1.isOpen_compl
  have hCc : IsClosed C := isClosed_biInter fun l _ => (U l).isOpen.isClosed_compl
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := LevCover.exists_sub (Z := Z ⊗ K) ⟨C, hCo⟩ hCc
  haveI := hVf; haveI := hVe
  obtain ⟨I, hIc, hI⟩ := LevCover.exists_image (i ≫ fst Z K)
  have hA : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ Z),
      Set.range z.left ⊆ (I : Set Z.left)ᶜ ↔ ∀ g : Over.mk x ⟶ o.A,
        (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ a, z ≫ et a = g := by
    intro k _ _ x z
    rw [range_sp_subset_compl, hI k x z]
    constructor
    · intro hno g hg
      by_contra hne
      push_neg at hne
      obtain ⟨y, hy, -⟩ := hrep _ g hg
      apply hno
      have hmem : Set.range (lift z y).left ⊆ C := by
        refine Set.subset_iInter₂ fun l hl => ?_
        obtain ⟨a, rfl⟩ := hl
        rw [range_sp_subset_compl, ← (hU _).2]
        intro h
        simp only [lift_snd, lift_fst_assoc] at h
        apply hne a
        rw [← hy, h, Category.assoc, hlam]
      obtain ⟨w, hw⟩ := (hV _ (lift z y)).1 hmem
      exact ⟨w, by rw [← Category.assoc, hw, lift_fst]⟩
    · rintro hall ⟨w, hw⟩
      obtain ⟨a, ha⟩ := hall ((w ≫ i) ≫ snd Z K ≫ κ) (hkc _ _ _ _ (hkc _ _ _ _ hκ))
      have hs : (w ≫ i) ≫ snd Z K = (w ≫ i) ≫ fst Z K ≫ lam a := by
        apply huniq
        have := ha
        rw [← hw] at this
        simpa only [Category.assoc, hlam] using this.symm
      have h1 := ((hU (lam a)).2 _ _).1 hs
      have h2 : Set.range (w ≫ i).left ⊆ C := (hV _ _).2 ⟨w, rfl⟩
      haveI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum k))
      have h3 := h2 ⟨default, rfl⟩
      exact Set.mem_iInter₂.1 h3 (lam a) ⟨a, rfl⟩ (h1 ⟨default, rfl⟩)
  refine ⟨⟨(I : Set Z.left)ᶜ, hIc.isOpen_compl⟩, I.isOpen.isClosed_compl, fun T' h => ?_⟩
  constructor
  · intro H
    apply LevCover.range_subset_of_geom h
    intro k _ _ x y
    have e : (y ≫ h).left = ((Over.homMk y.left rfl : Over.mk (y.left ≫ T'.hom) ⟶ T') ≫ h).left := rfl
    rw [e]
    change _ ⊆ (I : Set Z.left)ᶜ
    rw [hA]
    intro g hg
    obtain ⟨a, ha⟩ := H k y.left g hg
    exact ⟨a, by rw [Category.assoc]; exact ha⟩
  · intro H k _ _ xp g hg
    have hsub : Set.range ((Over.homMk xp rfl : Over.mk (xp ≫ T'.hom) ⟶ T') ≫ h).left ⊆ (I : Set Z.left)ᶜ := by
      rintro _ ⟨t, rfl⟩
      exact H ⟨xp t, by simp⟩
    obtain ⟨a, ha⟩ := (hA k (xp ≫ T'.hom) _).1 hsub g hg
    exact ⟨a, by rw [← Category.assoc]; exact ha⟩

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZero
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

theorem coeff_at2_x1_x2_eq_zero_of_third_ne_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ) (he : e ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  classical
  let g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g := by
    funext s; rcases s with s | s <;> rfl
  have h1 : at2 c x1 x2 = rename g c := by
    rw [rename_eq_subst, ← hg]; rfl
  rw [h1]
  apply coeff_rename_eq_zero
  rintro ⟨v, hv⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h; push_neg at h; exact he (Finsupp.ext h)
  apply hi
  have h2 := congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv
  rw [Finsupp.mapDomain_notin_range] at h2
  · simpa using h2.symm
  · rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFinsuppProdConstFreeEqZeroOfDegreeLt
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivMono

theorem coeff_finsuppProd_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) (u : τ → MvPowerSeries σ R), (∀ j, constantCoeff (u j) = 0) →
      ∀ (α : τ →₀ ℕ) (β : σ →₀ ℕ), β.degree < α.degree → coeff β (α.prod fun j e => u j ^ e) = 0 := by
  intro R _ σ τ u hu α β hβ
  apply coeff_of_lt_order
  have hle : ((α.degree : ℕ) : ℕ∞) ≤ (α.prod fun j e => u j ^ e).order := by
    unfold Finsupp.prod
    refine le_trans ?_ (le_order_prod (fun j => u j ^ α j) α.support)
    rw [Finsupp.degree_apply, Nat.cast_sum]
    exact Finset.sum_le_sum fun j _ => le_order_pow_of_constantCoeff_eq_zero (α j) (hu j)
  exact lt_of_lt_of_le (by exact_mod_cast hβ) hle

end GlobalTheory.DivMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOne
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.OpLin

variable {R : Type} [CommRing R]

theorem degree_eq_one {σ : Type} [Fintype σ] {D : σ →₀ ℕ} (h : D.degree = 1) :
    ∃ s, D = Finsupp.single s 1 := by
  classical
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

theorem le_order_prod_pow {σ τ : Type} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (D : σ →₀ ℕ) :
    (D.degree : ℕ∞) ≤ (D.prod fun s e => a s ^ e).order := by
  refine le_trans ?_ (le_order_prod _ _)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (ha s)

theorem coeff_subst_of_degree_le_one {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0)
    {β : τ →₀ ℕ} (hβ : β.degree ≤ 1) :
    coeff β (subst a f) = ∑ s, coeff (Finsupp.single s 1) f * coeff β (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hs]
  have hsupp : (Function.support fun D : σ →₀ ℕ =>
      coeff D f • coeff β (D.prod fun s e => a s ^ e)) ⊆
      ((Finset.univ.image fun s : σ => Finsupp.single s 1 : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support] at hD
    have h0 : D ≠ 0 := by
      rintro rfl
      apply hD
      rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    have h1 : D.degree ≤ 1 := by
      by_contra hlt
      push_neg at hlt
      apply hD
      rw [coeff_of_lt_order (lt_of_lt_of_le ?_ (le_order_prod_pow ha D)), smul_zero]
      exact_mod_cast lt_of_le_of_lt hβ hlt
    have h2 : D.degree = 1 := by
      have : D.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff D).1 h)
      omega
    obtain ⟨s, rfl⟩ := degree_eq_one h2
    simp
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun s _ t _ h => Finsupp.single_left_injective one_ne_zero h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_single_index (by simp), pow_one, smul_eq_mul]

end GlobalTheory.QLog.OpLin

namespace GlobalTheory.QLog.OpLin

variable {B O : Type} [CommRing B] [CommRing O] {d : ℕ}

theorem coeff_inl {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single j 1)) (congrFun hμ.unit i)
  simp only [op, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero, eq_comm] using h

theorem coeff_inr {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  rw [← h, ← coeff_inl hμ i j]
  simp [coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type}
    (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) →
    (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 →
    coeff β (op μ u v i) = coeff β (u i + v i) := by
  intro B O _ _ θ d μ hμ τ u v hu hv i β hβ
  classical
  simp only [op, at2]
  rw [coeff_subst_of_degree_le_one (by rintro (s | s); exacts [hu s, hv s]) (hμ.const i) hβ,
    Fintype.sum_sum_type, map_add]
  simp [coeff_inl hμ, coeff_inr hμ]

end GlobalTheory.QLog.OpLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPLogarithmsEqInvFrobeniusMatrix
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCoef

theorem coeff_frob_single (p : ℕ) [hp : Fact p.Prime] {Q : Type} [CommRing Q] {d : ℕ}
    (s : Q →+* Q) (f : MvPowerSeries (Fin d) Q) (j : Fin d) :
    coeff (Finsupp.single j p) (frob p s f) = s (lin f j) := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hs : HasSubst (fun i => (X i : MvPowerSeries (Fin d) Q) ^ p) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hp0]
  rw [frob, coeff_subst hs]
  have key : ∀ e : Fin d →₀ ℕ, (e.prod fun i n => ((X i : MvPowerSeries (Fin d) Q) ^ p) ^ n) =
      monomial (p • e) 1 := by
    intro e
    induction e using Finsupp.induction with
    | zero => simp
    | single_add i n e hi hn ih =>
      rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index
        (by simp), ← pow_mul, X_pow_eq, monomial_mul_monomial, one_mul, smul_add,
        Finsupp.smul_single, smul_eq_mul]
  simp_rw [key]
  rw [finsum_eq_single _ (Finsupp.single j 1)]
  · rw [coeff_monomial, if_pos (by rw [Finsupp.smul_single, smul_eq_mul, mul_one]), smul_eq_mul,
      mul_one, coeff_map, lin]
  · intro e he
    rw [coeff_monomial, if_neg, smul_zero]
    intro h
    apply he
    ext i
    have := congrArg (fun g => g i) h
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at this ⊢
    split_ifs at this ⊢ with h1
    · exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (this.symm.trans (mul_one p).symm)
    · exact (mul_eq_zero.1 this.symm).resolve_left hp0

theorem coef_logs_inv_frob : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  intro p _ B Q _ _ _ s σ hs _ d k e U hU h hlin hint
  classical
  set x : Fin d → Fin d ⊕ Fin k → Q := fun j l => (p : Q) * coeff (Finsupp.single j p) (e l) with hx
  have hD : ∀ l i, (U * blk d k (p : B) 1) l i =
      U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i := by
    intro l i
    simp [blk, Matrix.mul_diagonal]
  have hco : ∀ i j, coeff (Finsupp.single j p)
      (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) =
      s (lin (e i) j) - ∑ l, algebraMap B Q (U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i) *
        coeff (Finsupp.single j p) (e l) := by
    intro i j
    rw [map_sub, GlobalTheory.FrobCoef.coeff_frob_single, comb, map_sum]
    simp_rw [coeff_smul, hD]
  have key : ∀ j, ∃ y : Fin d ⊕ Fin k → B, (∀ i, ∑ l, algebraMap B Q (U l i) * x j l =
      algebraMap B Q (y i)) ∧ ∀ i, ∃ t, y i - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
    intro j
    have H : ∀ i, ∃ yi : B, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q yi ∧
        ∃ t, yi - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
      rintro (a | r)
      · obtain ⟨b, hb, hbe⟩ := (h (Sum.inl a)).2 a rfl (Finsupp.single j p)
        obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.1 hb
        rw [hco, hlin] at hbe
        refine ⟨(Pi.single a (1 : B) : Fin d → B) j - β * p, ?_, -β, ?_⟩
        · have h1 : s ((Pi.single a (1 : Q) : Fin d → Q) j) = algebraMap B Q ((Pi.single a (1 : B) : Fin d → B) j) := by
            by_cases haj : j = a
            · subst haj; simp
            · simp [Pi.single_apply, haj]
          have hS : ∑ l, algebraMap B Q (U l (Sum.inl a)) * x j l = ∑ l, algebraMap B Q
              (U l (Sum.inl a) * (p : B)) * coeff (Finsupp.single j p) (e l) :=
            Finset.sum_congr rfl fun l _ => by simp only [hx, Sum.elim_inl, map_mul, map_natCast]; ring
          simp only [Sum.elim_inl] at hbe
          rw [hS, map_sub, ← h1]
          linear_combination -hbe
        · by_cases haj : a = j
          · subst haj; simp; ring
          · simp [Pi.single_apply, haj, Ne.symm haj]; ring
      · obtain ⟨b1, -, hb1⟩ := (h (Sum.inr r)).1 (Finsupp.single j p)
        obtain ⟨b0, hb0⟩ := hint (Sum.inr r) j
        rw [hco, hb0, hs] at hb1
        refine ⟨p * (σ b0 - b1), ?_, σ b0 - b1, by simp⟩
        simp only [Sum.elim_inr, mul_one] at hb1
        have : ∑ l, algebraMap B Q (U l (Sum.inr r)) * coeff (Finsupp.single j p) (e l) =
            algebraMap B Q (σ b0 - b1) := by
          rw [map_sub, ← hb1]; ring
        simp only [hx, map_mul, map_natCast, ← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    choose y hy1 hy2 using H
    exact ⟨y, hy1, hy2⟩
  choose y hy1 hy2 using key
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  refine ⟨fun a j => ∑ i, U⁻¹ i (Sum.inl a) * y j i, fun a j => ⟨?_, ?_⟩⟩
  · have : ∀ m, algebraMap B Q (∑ i, U⁻¹ i m * y j i) = x j m := by
      intro m
      calc algebraMap B Q (∑ i, U⁻¹ i m * y j i)
          = ∑ i, algebraMap B Q (U⁻¹ i m) * ∑ l, algebraMap B Q (U l i) * x j l := by
            simp only [map_sum, map_mul, hy1]
        _ = ∑ l, algebraMap B Q ((U * U⁻¹) l m) * x j l := by
            simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x j m := by
            rw [hUU]
            simp [Matrix.one_apply]
    exact this _
  · choose t ht using hy2 j
    refine ⟨∑ i, U⁻¹ i (Sum.inl a) * t i, ?_⟩
    have h1 : U⁻¹ (Sum.inl j) (Sum.inl a) = ∑ i, U⁻¹ i (Sum.inl a) * (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i := by
      simp [Pi.single_apply]
    rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ht i]; ring

end GlobalTheory.FrobCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsMemIdeal
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.IdealAt2

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal : ∀ (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    (∀ α, coeff α t ∈ I) → ∀ α, coeff α (at2 t u v) ∈ I := by
  intro R _ d τ I t u v hu hv ht α
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]
  rw [at2, coeff_subst hs]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun x y hx hy => I.add_mem hx hy) ?_
  intro e
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (ht e)

end GlobalTheory.IdealAt2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZero
section
open MvPowerSeries

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_at2_x2_x3_eq_zero_of_first_ne_zero {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (a b e : Fin d →₀ ℕ) (ha : a ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  classical
  have hX : ∀ s, Sum.elim (x2 (R := R) (d := d)) x3 s
      = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by
    intro s; cases s <;> rfl
  have hs : HasSubst (Sum.elim (x2 (R := R) (d := d)) x3) :=
    hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (Finsupp.ext h)
  unfold at2
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  have key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧
      (α.prod fun s k => (Sum.elim (x2 (R := R) (d := d)) x3 s) ^ k) = monomial β 1 := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ,
      β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_
    · rintro f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      exact ⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩
    · exact ⟨0, rfl, (monomial_zero_one).symm⟩
    · intro s _
      refine ⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩
      · cases s <;> simp
      · dsimp only
        rw [hX, X_pow_eq]
  obtain ⟨β, hβ, hp⟩ := key
  rw [hp, coeff_monomial_ne, smul_zero]
  intro h
  apply hi
  have := congrArg (fun w => w (Sum.inl i)) h
  simpa [hβ] using this

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePairStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m)))) = if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) + Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  first | exact @GlobalTheory.coeff_at2_single_X_inl_inr | exact GlobalTheory.coeff_at2_single_X_inl_inr | (intros; apply GlobalTheory.coeff_at2_single_X_inl_inr <;> assumption)
end

